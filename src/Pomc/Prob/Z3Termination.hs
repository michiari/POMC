{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuerySCC
                               ) where

import Prelude hiding (LT, GT)

import Pomc.Prec (Prec(..))
import Pomc.Check (EncPrecFunc)
import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)

import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as ZS

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, unless, when, forM_, forM)
import Control.Monad.ST (RealWorld)
import Pomc.Z3T (liftSTtoIO)

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as Map

import qualified Data.Map as GeneralMap
import qualified Data.HashTable.IO as HT
import Data.Maybe(fromJust, isJust, isNothing)
import qualified Data.Vector.Mutable as MV
import Data.Vector((!))
import qualified Data.Vector as V
import Data.Ratio (approxRational)

import Z3.Monad
import Data.IORef (IORef, newIORef, modifyIORef', readIORef, writeIORef)

import Data.STRef (STRef, modifySTRef')
import qualified Pomc.IOMapMap as MM

-- import qualified Debug.Trace as DBG

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = (HT.BasicHashTable VarKey AST, IntSet, Bool)

--helpers
encodeTransition :: MonadZ3 z3 => Edge -> AST -> z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

mkOp1 :: MonadZ3 z3 => ([AST] -> z3 AST) -> [AST] -> z3 AST
mkOp1 _ [ast] = return ast
mkOp1 mkOp asts = mkOp asts

mkAdd1 :: MonadZ3 z3 => [AST] -> z3 AST
mkAdd1 = mkOp1 mkAdd

mkMul1 :: MonadZ3 z3 => [AST] -> z3 AST
mkMul1 = mkOp1 mkMul

-- (Z3 Var, was it already present?)
lookupVar :: MonadZ3 z3
          => VarMap -> (AugEqMap EqMapNumbersType, AugEqMap EqMapNumbersType) -> VarKey
          -> z3 (Maybe (AST, Bool))
lookupVar (varMap, sccMembers, encodeInitial) (leqMap, uEqMap) key = do
  maybeVar <- liftIO $ HT.lookup varMap key
  let cases
        | isJust maybeVar = return $ Just (fromJust maybeVar, True)
        | snd key == -1 && encodeInitial = do
            addFixpEq leqMap key (PopEq 1)
            addFixpEq uEqMap key (PopEq 1)
            var <- mkRealNum (1 :: EqMapNumbersType)
            liftIO $ HT.insert varMap key var
            return $ Just (var, True)
        | IntSet.notMember (fst key) sccMembers = return Nothing
        | otherwise = do -- it might happen that we discover new variables, in case of cycles that keep pushing
            var <- mkFreshRealVar $ show key
            liftIO $ HT.insert varMap key var
            return $ Just (var, False)
  cases

-- end helpers

encode :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
       => [(Int, Int)]
       -> VarMap
       -> (AugEqMap EqMapNumbersType, AugEqMap EqMapNumbersType)
       -> SupportGraph state
       -> EncPrecFunc
       -> (AST -> AST -> z3 AST)
       -> Bool
       -> Int
       -> z3 Int
encode [] _ _ _ _ _ _ count = return count
encode ((gnId_, rightContext):unencoded) varMap@(m, _, _) (lowerEqMap, upperEqMap) graph precFun mkComp useZ3 count = do
  let varKey = (gnId_, rightContext)
  var <- liftIO $ fromJust <$> HT.lookup m varKey
  let gn = graph ! gnId_
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        | isNothing g && gnId_ /= 0  =
            error "Never encode semiconfs with bottom stack, apart from the initial one"

        | isNothing g || precRel == Just Yield =
            encodePush graph varMap (lowerEqMap, upperEqMap) mkComp gn varKey var useZ3

        | precRel == Just Equal =
            encodeShift varMap (lowerEqMap, upperEqMap) mkComp gn varKey var useZ3

        | precRel == Just Take = do
            let e = Map.findWithDefault 0 rightContext (popContexts gn)
            when useZ3 $ do
              solvedVar <- mkRealNum e
              liftIO $ HT.insert m varKey solvedVar

            addFixpEq lowerEqMap varKey $ PopEq $ fromRational e
            addFixpEq upperEqMap varKey $ PopEq $ fromRational e
            return [] -- pop transitions do not generate new variables

        | otherwise = fail "unexpected prec rel"

  newUnencoded <- cases
  encode (newUnencoded ++ unencoded) varMap (lowerEqMap, upperEqMap) graph precFun mkComp useZ3 (count + 1)

-- encoding helpers --
encodePush :: (MonadZ3 z3, Eq state, Hashable state, Show state)
           => SupportGraph state
           -> VarMap
           -> (AugEqMap EqMapNumbersType, AugEqMap EqMapNumbersType)
           -> (AST -> AST -> z3 AST)
           -> GraphNode state
           -> VarKey
           -> AST
           -> Bool
           -> z3 [(Int, Int)]
encodePush graph varMap@(m, _, _) (lowerEqMap, upperEqMap) mkComp  gn varKey@(_, rightContext) var useZ3 =
  let closeSummaries pushGn (currs, newVars, terms) e = do
        let supportGn = graph ! (to e)
            varsIds = [(gnId pushGn, getId . fst . semiconf $ supportGn), (gnId supportGn, rightContext)]
        maybeTerms <- mapM (lookupVar varMap (lowerEqMap, upperEqMap)) varsIds
        let newUnencoded = [(gnId__, rightContext_) | (Just (_, False), (gnId__, rightContext_)) <- zip maybeTerms varsIds]
                           ++ newVars
        if any isNothing maybeTerms
          then return (currs, newUnencoded, terms) -- One variable is null, so we don't add the term
          else do
          eq <- mkMul1 (map (fst . fromJust ) maybeTerms)
          return (eq:currs, newUnencoded, varsIds:terms)

      pushEnc (currs, vars, terms) e = do
        (equations, unencodedVars, varTerms) <- foldM (closeSummaries (graph ! to e)) ([], [], []) (supportEdges gn)
        if null equations
          then return (currs, unencodedVars ++ vars, terms)
          else do
            transition <- encodeTransition e =<< mkAdd1 equations
            return ( transition:currs
                    , unencodedVars ++ vars
                    , (map (\[v1, v2] -> (prob e, v1, v2)) varTerms):terms
                    )
  in do
    (transitions, unencoded_vars, terms) <- foldM pushEnc ([], [], []) (internalEdges gn)
    -- logDebugN $ show varKey ++ " = PushEq " ++ show terms
    let emptyPush = all null terms
        pushEq | emptyPush = PopEq 0
               | otherwise = PushEq $ concat terms
    when useZ3 $ if emptyPush
        then do
          solvedVar <- mkRealNum (0 :: Rational)
          liftIO $ HT.insert m varKey solvedVar
          eq <- mkEq var solvedVar
          assert eq
        else do
          eq <- mkComp var =<< mkAdd1 transitions -- generate the equation for this semiconf
          --eqString <- astToString eq
          -- logDebugN $ "Asserting Push equation: " ++ eqString
          assert eq

    addFixpEq upperEqMap varKey pushEq
    addFixpEq lowerEqMap varKey pushEq
    return unencoded_vars

encodeShift :: (MonadZ3 z3, Eq state, Hashable state, Show state)
            => VarMap
            -> (AugEqMap EqMapNumbersType, AugEqMap EqMapNumbersType)
            -> (AST -> AST -> z3 AST)
            -> GraphNode state
            -> VarKey
            -> AST
            -> Bool
            -> z3 [(Int, Int)]
encodeShift varMap (lowerEqMap, upperEqMap) mkComp gn varKey@(_, rightContext) var useZ3 =
  let shiftEnc (currs, newVars, terms) e = do
        let target = (to e, rightContext)
        maybeTerm <- lookupVar varMap (lowerEqMap, upperEqMap) target
        if isNothing maybeTerm
          then return (currs, newVars, terms)
          else do
            let (toVar, alreadyEncoded) = fromJust maybeTerm
                newUnencoded = if alreadyEncoded then newVars else target:newVars
            trans <- encodeTransition e toVar
            return (trans:currs, newUnencoded, (prob e, target):terms)
  in do
    (transitions, unencoded_vars, terms) <- foldM shiftEnc ([], [], []) (internalEdges gn)
    when useZ3 $ do
      eq <- mkComp var =<< mkAdd1 transitions -- generate the equation for this semiconf
      --eqString <- astToString eq
      -- logDebugN $ "Asserting Shift equation: " ++ eqString
      assert eq

    -- logDebugN $ show varKey ++ " = ShiftEq " ++ show terms
    let shiftEq | null terms = error "shift semiconfs should go somewhere!"
                | otherwise = ShiftEq terms
    addFixpEq upperEqMap varKey shiftEq
    addFixpEq lowerEqMap varKey shiftEq
    return unencoded_vars
-- end

---------------------------------------------------------------------------------------------------
-- compute termination probabilities, but do it with a backward analysis for every SCC --
---------------------------------------------------------------------------------------------------

type SuccessorsPopContexts = IntSet

type PartialVarMap = (HT.BasicHashTable VarKey AST, Bool)

data DeficientGlobals state = DeficientGlobals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , successorsCntxs :: MV.IOVector SuccessorsPopContexts
  , mustReachPop :: IORef IntSet
  , partialVarMap :: PartialVarMap
  , rewVarMap :: RewVarMap
  , upperEqMap :: AugEqMap EqMapNumbersType
  , lowerEqMap :: AugEqMap EqMapNumbersType
  , eps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

terminationQuerySCC :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
                    => SupportGraph state
                    -> EncPrecFunc
                    -> TermQuery
                    -> STRef RealWorld Stats
                    -> z3 (TermResult, IntSet)
terminationQuerySCC suppGraph precFun query oldStats = do
  newSS              <- liftIO ZS.new
  newBS              <- liftIO ZS.new
  newIVec            <- liftIO $ MV.replicate (V.length suppGraph) 0
  newSuccessorsCntxs <- liftIO $ MV.replicate (V.length suppGraph) IntSet.empty
  newMap <- liftIO HT.new
  newUpperEqMap <- liftIO MM.empty
  newLowerEqMap <- liftIO MM.empty
  newLowerLiveVars <- liftIO $ newIORef Set.empty
  newUpperLiveVars <- liftIO $ newIORef Set.empty
  emptyMustReachPop <- liftIO $ newIORef IntSet.empty
  newRewVarMap <- liftIO HT.new
  newEps <- liftIO $ newIORef defaultEps
  let globals = DeficientGlobals { sStack = newSS
                                , bStack = newBS
                                , iVector = newIVec
                                , successorsCntxs = newSuccessorsCntxs
                                , mustReachPop = emptyMustReachPop
                                , partialVarMap = (newMap, encodeInitialSemiconf query)
                                , rewVarMap = newRewVarMap
                                , upperEqMap = (newUpperEqMap, newUpperLiveVars)
                                , lowerEqMap = (newLowerEqMap, newLowerLiveVars)
                                , eps = newEps
                                , stats = oldStats
                                }
  -- setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT

  -- perform the Gabow algorithm to compute all termination probabilities
  let (useZ3, exactEq) = case solver query of
        OVI -> (False, False)
        SMTWithHints -> (True, False)
        ExactSMTWithHints -> (True, True)
      gn = suppGraph ! 0

  addtoPath globals gn
  (popCntx, isAST) <- dfs suppGraph globals precFun (useZ3, exactEq) gn
  unless (IntSet.null popCntx) $ error $ "Pop contexts detected: " ++ show popCntx ++ " but the initial state cannot reach any pop"

  -- returning the computed values
  currentEps <- liftIO $ readIORef (eps globals)
  mustReachPopIdxs <- liftIO $ readIORef (mustReachPop globals)
  let actualEps = min defaultEps $ currentEps * currentEps
      intervalLogic (_, ub) Lt p = ub < p
      intervalLogic (lb, _) Gt p = lb > p
      intervalLogic (_, ub) Le p = ub <= p
      intervalLogic (lb, _) Ge p = lb >= p
      readResults (ApproxAllQuery SMTWithHints) = do
        upperProbRationalMap <- GeneralMap.fromList <$> (mapM (\(varKey, varAST) -> do
            pRational <- extractUpperProb varAST
            return (varKey, pRational)) =<< liftIO (HT.toList newMap))
        lowerProbMap <- liftIO $ GeneralMap.map (\(PopEq d) -> d) <$> MM.foldMaps newLowerEqMap
        let lowerProbRationalMap = GeneralMap.map (\v -> approxRational (v - actualEps) actualEps) lowerProbMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery SMTWithHints) = do
        ub <- if isAST then return 1 else extractUpperProb . fromJust =<< liftIO (HT.lookup newMap (0,-1))
        lb <- if isAST then return 1 else liftIO $ (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> MM.lookupValue newLowerEqMap 0 (-1)
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound SMTWithHints) = do
        ub <- if isAST then return 1 else extractUpperProb . fromJust =<< liftIO (HT.lookup newMap (0,-1))
        logInfoN $ "Computed upper bound: " ++ show ub
        lb <- if isAST then return 1 else liftIO $  (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> MM.lookupValue newLowerEqMap 0 (-1)
        logInfoN $ "Computed lower bound: " ++ show lb
        logInfoN $ "Comparing: " ++ show comp ++ " " ++ show bound
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)
      readResults (ApproxAllQuery ExactSMTWithHints) = readResults (ApproxAllQuery SMTWithHints)
      readResults (ApproxSingleQuery ExactSMTWithHints) = readResults (ApproxSingleQuery SMTWithHints)
      readResults (CompQuery comp bound ExactSMTWithHints) = readResults (CompQuery comp bound SMTWithHints)
      readResults (ApproxAllQuery OVI) = liftIO $ do
        upperProbMap <- GeneralMap.map (\(PopEq d) -> d) <$> MM.foldMaps newUpperEqMap
        let upperProbRationalMap = GeneralMap.map (\v -> approxRational (v + actualEps) actualEps) upperProbMap
        lowerProbMap <- GeneralMap.map (\(PopEq d) -> d) <$> MM.foldMaps newLowerEqMap
        let lowerProbRationalMap = GeneralMap.map (\v -> approxRational (v - actualEps) actualEps) lowerProbMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery OVI) = liftIO $ do
        ub <- if isAST then return 1 else (\(PopEq d) -> approxRational (d + actualEps) actualEps) . fromJust <$> MM.lookupValue newUpperEqMap  0 (-1)
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> MM.lookupValue newLowerEqMap  0 (-1)
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound OVI) = liftIO $ do
        ub <- if isAST then return 1 else (\(PopEq d) -> approxRational (d + actualEps) actualEps) . fromJust <$> MM.lookupValue newUpperEqMap  0 (-1)
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> MM.lookupValue newLowerEqMap  0 (-1)
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)

  lowerVars <- liftIO $ MM.foldMaps newLowerEqMap
  upperVars <- liftIO $ MM.foldMaps newUpperEqMap
  logInfoN $ "Number of variables for lower bound: " ++ show (GeneralMap.size lowerVars)
  logInfoN $ "Number of variables for upper bound: " ++ show (GeneralMap.size upperVars)
  readResults query

dfs :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
    => SupportGraph state
    -> DeficientGlobals state
    -> EncPrecFunc
    -> (Bool, Bool)
    -> GraphNode state
    -> z3 (SuccessorsPopContexts, Bool)
dfs suppGraph globals precFun (useZ3, exactEq) gn =
  let cases nextNode iVal
        | (iVal == 0) = addtoPath globals nextNode >> dfs suppGraph globals precFun (useZ3, exactEq) nextNode
        | (iVal < 0)  = liftIO $ do
            popCntxs <-  MV.unsafeRead (successorsCntxs globals) (gnId nextNode)
            mrPop <- IntSet.member (gnId nextNode) <$> readIORef (mustReachPop globals)
            return (popCntxs, mrPop)
        | (iVal > 0)  = merge globals nextNode >> return (IntSet.empty, True)
        | otherwise = error "unreachable error"
      follow e = liftIO (MV.unsafeRead (iVector globals) (to e)) >>= cases (suppGraph ! to e)
  in do
    res <- forM (Set.toList $ internalEdges gn) follow
    let dPopCntxs = IntSet.unions (map fst res)
        dMustReachPop = all snd res
        computeActualRes
          | not . Set.null $ supportEdges gn = do
              newRes <- forM (Set.toList $ supportEdges gn) follow
              let actualDPopCntxs = IntSet.unions (map fst newRes)
              if gnId gn == 0
                then return (actualDPopCntxs, dMustReachPop)
                else return (actualDPopCntxs, dMustReachPop && all snd newRes)
          | not . Map.null $ popContexts gn = return (IntSet.fromList . Map.keys $ popContexts gn, True)
          | otherwise = return (dPopCntxs, dMustReachPop)
    (dActualPopCntxs, dActualMustReachPop) <- computeActualRes
    createComponent suppGraph globals gn (dActualPopCntxs, dActualMustReachPop) precFun (useZ3, exactEq)


-- helpers
addtoPath :: MonadZ3 z3 => DeficientGlobals state -> GraphNode state -> z3 ()
addtoPath globals gn = liftIO $ do
  ZS.push (sStack globals) (gnId gn)
  sSize <- ZS.size $ sStack globals
  MV.unsafeWrite (iVector globals) (gnId gn) sSize
  ZS.push (bStack globals) sSize

merge :: MonadZ3 z3 => DeficientGlobals state -> GraphNode state -> z3 ()
merge globals gn = liftIO $ do
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  ZS.popWhile_ (bStack globals) (iVal <)

createComponent :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
                => SupportGraph state
                -> DeficientGlobals state
                -> GraphNode state
                -> (SuccessorsPopContexts, Bool)
                -> EncPrecFunc
                -> (Bool, Bool)
                -> z3 (SuccessorsPopContexts, Bool)
createComponent suppGraph globals gn (popContxs, dMustReachPop) precFun (useZ3, exactEq) = do
  topB <- liftIO $ ZS.peek $ bStack globals
  iVal <- liftIO $ MV.unsafeRead (iVector globals) (gnId gn)
  let (varMap, encodeInitial) = partialVarMap globals
      lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals
      mkComp = (if exactEq then mkEq else mkGe)
      createC = do
        liftIO $ ZS.pop_ (bStack globals)
        sSize <- liftIO $ ZS.size $ sStack globals
        poppedEdges <- liftIO $ ZS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        logDebugN $ "Popped Semiconfigurations: " ++ show poppedEdges
        logDebugN $ "Pop contexts: " ++ show popContxs
        logDebugN $ "Length of current SCC: " ++ show (length poppedEdges)
        forM_ poppedEdges $ \e -> do
          liftIO $ MV.unsafeWrite (iVector globals) e (-1)
          liftIO $ MV.unsafeWrite (successorsCntxs globals) e popContxs
        return poppedEdges
      doEncode poppedEdges  = do
        let toEncode = [(gnId_, rc) | gnId_ <- poppedEdges, rc <- IntSet.toList popContxs]
            sccMembers = IntSet.fromList poppedEdges
        insertedVars <- map (snd . fromJust) <$> forM toEncode (lookupVar (varMap, sccMembers, encodeInitial) (lEqMap, uEqMap))
        when (or insertedVars ) $ error "inserting a variable that has already been encoded"
        -- delete previous assertions and encoding the new ones
        reset 
        eqsCount <- encode toEncode (varMap, sccMembers, encodeInitial) (lowerEqMap globals, upperEqMap globals) suppGraph precFun mkComp useZ3 0
        liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCount = acc} -> s{ equationsCount = acc + eqsCount}
        actualMustReachPop <- solveSCCQuery suppGraph dMustReachPop (varMap, sccMembers, encodeInitial) globals precFun (useZ3, exactEq)
        when actualMustReachPop $ forM_ poppedEdges $ \e -> liftIO $ modifyIORef' (mustReachPop globals) $ IntSet.insert e
        return (popContxs, actualMustReachPop)
      doNotEncode = do
        if gnId gn == 0 && encodeInitial
          then do -- for the initial semiconf, encode anyway
            var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
            liftIO $ HT.insert varMap (0, -1) var
            reset 
            eqsCount <- encode [(0, -1)] (varMap, IntSet.singleton 0, encodeInitial) (lowerEqMap globals, upperEqMap globals) suppGraph precFun mkComp useZ3 0
            liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCount = acc} -> s{ equationsCount = acc + eqsCount}
            actualMustReachPop <- solveSCCQuery suppGraph dMustReachPop (varMap, IntSet.singleton 0, encodeInitial)  globals precFun (useZ3, exactEq)
            return (popContxs, actualMustReachPop)
          else do
            liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCount = acc} -> s{sccCount = acc + 1}
            return (popContxs, False)
      cases
        | iVal /= topB = return (popContxs, dMustReachPop)
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >> doNotEncode -- cannot reach a pop
  cases

-- params:
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveSCCQuery :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
              => SupportGraph state -> Bool -> VarMap -> DeficientGlobals state -> EncPrecFunc -> (Bool, Bool) -> z3 Bool
solveSCCQuery suppGraph dMustReachPop varMap@(m,  sccMembers, _) globals precFun (useZ3, exactEq) = do
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCount = acc} -> s{sccCount = acc + 1}
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCount = acc} -> s{largestSCCSemiconfsCount = max acc (IntSet.size sccMembers)}
  --logDebugN $ "New variables of this SCC: " ++ show variables
  currentEps <- liftIO $ readIORef (eps globals)

  let lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals
      rVarMap = rewVarMap globals
      augTolerance = 100 * defaultTolerance
      sccLen = IntSet.size sccMembers
      cases unsolvedVars
        | null unsolvedVars = logDebugN "No equation system has to be solved here, just propagated all the values." >> return []
        | useZ3 = updateLowerBound >> updateUpperBoundsZ3
        | otherwise = updateLowerBound >> updateUpperBoundsOVI
      updateLowerBound = do
        -- updating lower bounds
        approxVec <- approxFixp lEqMap defaultEps defaultMaxIters
        liftIO $ HT.mapM_ (\(varKey, p) -> addFixpEq lEqMap varKey (PopEq p)) approxVec
      --
      doAssert approxFracVec currentEps = do
        push -- create a backtracking point
        epsReal <- mkRealNum currentEps

        forM_ approxFracVec (\(varKey, pRational) -> do
            var <- liftIO $ fromJust <$> HT.lookup m varKey
            pReal <- mkRealNum pRational
            assert =<< mkGe var pReal
            assert =<< mkLe var =<< mkAdd [pReal, epsReal])

        -- solverDump <- solverToString
        -- liftIO $ writeFile ("solver_dump_" ++ show currentEps ++ ".smt2") solverDump

        solverCheckAndGetModel >>= \case
          (Sat, Just model) -> return model
          (Unsat, _)
            | currentEps <= 1 -> do
                logDebugN $ "Unsat, backtrack. Current eps: " ++ show currentEps
                liftIO (writeIORef (eps globals) (2 * currentEps)) >> pop 1 >> doAssert approxFracVec (2 * currentEps) -- backtrack one point and restart
            | otherwise -> error "Maximum tolerance reached when solving SCC"
          _ -> error "Undefinite result when checking an SCC"
      --
      updateUpperBoundsZ3 = do
        startUpper <- startTimer
        logDebugN "Approximating via Value Iteration + z3"
        approxVec <- approxFixp uEqMap defaultEps defaultMaxIters
        approxFracVec <- toRationalProbVec defaultEps approxVec

        logDebugN "Asserting lower and upper bounds computed from value iteration, and getting a model"
        model <- doAssert approxFracVec (min defaultTolerance currentEps)

        -- actual updates
        upperBound <- liftIO (HT.toList approxVec) >>= foldM (\acc (varKey, _) -> do
          varAST <- liftIO $ fromJust <$> HT.lookup m varKey
          ubAST <- fromJust <$> eval model varAST
          pDouble <- extractUpperDouble ubAST
          liftIO $ HT.insert m varKey ubAST
          addFixpEq uEqMap varKey (PopEq pDouble)
          return ((varKey, pDouble):acc)
          ) []

        tUpper <- stopTimer startUpper upperBound
        liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
        return upperBound
      --
      updateUpperBoundsOVI = do
        startUpper <- startTimer
        logDebugN "Using OVI to update upper bounds"
        oviRes <- ovi defaultOVISettingsDouble uEqMap
        rCertified <- oviToRational defaultOVISettingsDouble uEqMap oviRes
        unless rCertified $ error "cannot deduce a rational certificate for this semiconf"
        unless (oviSuccess oviRes || rCertified) $ error "OVI was not successful in computing an upper bound on the termination probabilities"

        -- actual updates
        liftIO (HT.toList $ oviUpperBound oviRes) >>= mapM_ ( \(varKey, p) -> do
          let ub = min (1 :: Double) p
          ubAST <- mkRealNum ub
          liftIO $ HT.insert m varKey ubAST
          addFixpEq uEqMap varKey (PopEq p)
          ) 

        tUpper <- stopTimer startUpper True
        liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
        liftIO $ HT.toList (oviUpperBound oviRes)

  -- preprocessing phase
  _ <- preprocessApproxFixp lEqMap defaultEps (2 * sccLen)
  (updatedUpperVars, unsolvedVars) <- preprocessApproxFixp uEqMap defaultEps (sccLen + 1)
  forM_ updatedUpperVars $ \(varKey, p) -> do
    pAST <- mkRealNum (p :: Double)
    liftIO $ HT.insert m varKey pAST

  -- lEqMap and uEqMap have the same unsolved equations
  logDebugN $ "Number of live equations to be solved: " ++ show (length unsolvedVars) ++ " - unsolved variables: " ++ show unsolvedVars
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCNonTrivialEqsCount = acc } -> s{ largestSCCNonTrivialEqsCount = max acc (length unsolvedVars) }
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquationsCount = acc} -> s{nonTrivialEquationsCount = acc + length unsolvedVars}


  -- find bounds for this SCC
  upperBound <- cases unsolvedVars
  let upperBoundsTermProbs = Map.fromListWith (+) . map (\(key, ub) -> (fst key, ub)) $ (upperBound ++ updatedUpperVars)
  let upperBounds = GeneralMap.fromList upperBound
  logDebugN $ unlines
    [ "Computed upper bounds: " ++ show upperBounds
    , "Computed upper bounds on termination probabilities: " ++ show upperBoundsTermProbs
    , "Do all the descendant terminate almost surely? " ++ show dMustReachPop
    , "Are the upper bounds proving not AST? " ++ show (all (\(_,ub) -> ub < 1 - defaultTolerance) (Map.toList upperBoundsTermProbs))
    ]

  -- computing the PAST certificate (if needed)
  let nonASTprobs = all (\(_,ub) -> ub < 1 - augTolerance) (Map.toList upperBoundsTermProbs)
      aSTprobs = all (\(_,ub) -> ub > 1 - augTolerance) (Map.toList upperBoundsTermProbs)
      exactASTprobs = all (\(_,ub) -> ub > 1 - defaultTolerance) (Map.toList upperBoundsTermProbs)
      pASTCertCases
        | null unsolvedVars = return dMustReachPop -- just propagating
        | exactEq = return exactASTprobs
        | not dMustReachPop && aSTprobs = error "Descendants are not PAST but this SCC has termination upper bound equal to 1"
        | nonASTprobs = logDebugN "The upper bound is enough to prove non AST" >> return False
        | otherwise = do
          startPast <- startTimer
          forM_ (IntSet.toList sccMembers) $ \k -> do
              (_, alreadyEnc) <- lookupRewVar rVarMap k
              when alreadyEnc $ error "encoding a variable for a semiconf that has already been encoded"
          reset >> encodeReward (IntSet.toList sccMembers) varMap rVarMap suppGraph precFun mkGe
          pastRes <- withModel (\model -> forM (IntSet.toList sccMembers) $ \k -> do
                                  var <- liftIO $ fromJust <$> HT.lookup rVarMap k
                                  evaluated <- fromJust <$> eval model var
                                  liftIO $ HT.insert rVarMap k evaluated
                              ) >>= \case
            (Unsat, _) -> error "fail to prove PAST when some semiconfs have upper bounds on their termination equal to 1"
            (Sat, _) -> do
              unless aSTprobs $ error "Found a PAST certificate for non AST SCC!!"
              logDebugN "PAST certification succeeded!" >> return True
            _ -> error "undefined result when running the PAST certificate"

          tPast <- stopTimer startPast pastRes
          liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { pastTime = pastTime s + tPast })
          return pastRes
  pASTCertCases

--- REWARDS COMPUTATION for certificating PAST  ---------------------------------
type RewVarKey = Int
type RewVarMap = HT.BasicHashTable Int AST

-- (Z3 Var, was it already present?)
lookupRewVar :: MonadZ3 z3 => RewVarMap -> RewVarKey -> z3 (AST, Bool)
lookupRewVar rewVarMap key = do
  maybeVar <- liftIO $ HT.lookup rewVarMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      newVar <- mkFreshRealVar $ show key
      liftIO $ HT.insert rewVarMap key newVar
      return (newVar, False)
-- end helpers


encodeReward :: (MonadZ3 z3, MonadFail z3, Eq state, Hashable state, Show state)
             => [RewVarKey]
             -> VarMap
             -> RewVarMap
             -> SupportGraph state
             -> EncPrecFunc
             -> (AST -> AST -> z3 AST)
             -> z3 ()
encodeReward [] _ _ _ _ _ = return ()
encodeReward (gnId_:unencoded) varMap rewVarMap graph precFun mkComp = do
  rewVar <- liftIO $ fromJust <$> HT.lookup rewVarMap gnId_
  let gn = graph ! gnId_
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
          encodeRewPush graph varMap rewVarMap mkComp gn rewVar

        | precRel == Just Equal =
            encodeRewShift rewVarMap mkComp gn rewVar

        | precRel == Just Take = do
            assert =<< mkEq rewVar =<< mkRealNum (1 :: Prob)
            return [] -- pop transitions do not generate new variables

        | otherwise = fail "unexpected prec rel"

  newUnencoded <- cases
  encodeReward (newUnencoded ++ unencoded) varMap rewVarMap graph precFun mkComp

-- encoding helpers --
encodeRewPush :: (MonadZ3 z3, Eq state, Hashable state, Show state)
              => SupportGraph state
              -> VarMap
              -> RewVarMap
              -> (AST -> AST -> z3 AST)
              -> GraphNode state
              -> AST
              -> z3 [RewVarKey]
encodeRewPush graph (m, _ ,_) rewVarMap mkComp gn var =
  let closeSummaries pushGn (currs, unencoded_vars) e = do
        let supportGn = graph ! (to e)
        maybeTermProb <- liftIO $ HT.lookup m (gnId pushGn, getId . fst . semiconf $ supportGn)
        if isNothing maybeTermProb
          then return (currs, unencoded_vars)
          else do
            (summaryVar, alreadyEncoded) <- lookupRewVar rewVarMap (gnId supportGn)
            eq <- mkMul [fromJust maybeTermProb, summaryVar]
            return ( eq:currs
                  ,  if alreadyEncoded then unencoded_vars else (gnId supportGn):unencoded_vars
                  )
      pushEnc (currs, vars) e = do
        let pushGn = graph ! (to e)
        (pushVar, alreadyEncoded) <- lookupRewVar rewVarMap (gnId pushGn)
        (equations, unencoded_vars) <- foldM (closeSummaries pushGn) ([], []) (supportEdges gn)
        transition <- encodeTransition e =<< mkAdd (pushVar:equations)
        when (null equations) $ error "a push should terminate somehow, if we want to prove PAST"
        return ( transition:currs
               , if alreadyEncoded then unencoded_vars ++ vars else (gnId pushGn) : (unencoded_vars ++ vars)
               )
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions) -- generate the equation for this semiconf
    assert =<< mkGe var one
    return unencoded_vars

encodeRewShift :: (MonadZ3 z3, Eq state, Hashable state, Show state)
  => RewVarMap
  -> (AST -> AST -> z3 AST)
  -> GraphNode state
  -> AST
  -> z3 [RewVarKey]
encodeRewShift rewVarMap mkComp gn var =
  let shiftEnc (currs, new_vars) e = do
        let target = to e
        (toVar, alreadyEncoded) <- lookupRewVar rewVarMap target
        trans <- encodeTransition e toVar
        return ( trans:currs
            , if alreadyEncoded then new_vars else target:new_vars
            )
  in do
    (transitions, unencodedVars) <- foldM shiftEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions) -- generate the equation for this semiconf
    assert =<< mkGe var one
    return unencodedVars
