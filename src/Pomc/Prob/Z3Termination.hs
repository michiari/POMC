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

import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint
import Pomc.Prob.OVI (oviWithHints, oviToRationalWithHints, defaultOVISettingsDouble, OVIResult(..))

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as ZS

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, unless, when, forM_, forM)
import Control.Monad.ST (RealWorld, stToIO)

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

import qualified Debug.Trace as DBG
import Data.STRef (STRef, modifySTRef')

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = (HT.BasicHashTable VarKey AST, HT.BasicHashTable VarKey AST, IntSet, Bool)

--helpers
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

mkOp1 :: ([AST] -> Z3 AST) -> [AST] -> Z3 AST
mkOp1 _ [ast] = return ast
mkOp1 mkOp asts = mkOp asts

mkAdd1 :: [AST] -> Z3 AST
mkAdd1 = mkOp1 mkAdd

mkMul1 :: [AST] -> Z3 AST
mkMul1 = mkOp1 mkMul

-- (Z3 Var, was it already present?)
lookupVar :: VarMap -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType) -> VarKey -> Z3 (Maybe (AST, Bool))
lookupVar (varMap, newAdded, sccMembers, encodeInitial) (leqMap, uEqMap) key = do
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
        | otherwise = do -- it might happen that we discover new variables, in case of cicles that keep pushing
            var <- mkFreshRealVar $ show key
            liftIO $ HT.insert varMap key var
            liftIO $ HT.insert newAdded key var
            return $ Just (var, False)
  cases

-- end helpers

encode :: (Eq state, Hashable state, Show state)
      => [(Int, Int)]
      -> VarMap
      -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
      -> SupportGraph state
      -> EncPrecFunc
      -> (AST -> AST -> Z3 AST)
      -> Bool
      -> Z3 ()
encode [] _ _ _ _ _ _ = return ()
encode ((gnId_, rightContext):unencoded) varMap@(m, _, _, _) (lowerEqMap, upperEqMap) graph precFun mkComp useZ3 = do
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
  encode (newUnencoded ++ unencoded) varMap (lowerEqMap, upperEqMap) graph precFun mkComp useZ3

-- encoding helpers --
encodePush :: (Eq state, Hashable state, Show state)
           => SupportGraph state
           -> VarMap
           -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
           -> (AST -> AST -> Z3 AST)
           -> GraphNode state
           -> VarKey
           -> AST
           -> Bool
           -> Z3 [(Int, Int)]
encodePush graph varMap@(m, newAdded, _, _) (lowerEqMap, upperEqMap) mkComp  gn varKey@(_, rightContext) var useZ3 =
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
    --DBG.traceM $ show varKey ++ " = PushEq " ++ show terms
    let emptyPush = null (concat terms)
        pushEq |  emptyPush = PopEq 0
               | otherwise = PushEq $ concat terms
    when useZ3 $ if emptyPush
        then do
          solvedVar <- mkRealNum 0
          liftIO $ HT.insert m varKey solvedVar
          eq <- mkEq var solvedVar
          assert eq
        else do
          eq <- mkComp var =<< mkAdd1 transitions -- generate the equation for this semiconf
          --eqString <- astToString eq
          --DBG.traceM $ "Asserting Push equation: " ++ eqString
          assert eq
          assert =<< mkGe var =<< mkRealNum 0

    when emptyPush $ liftIO $ HT.delete newAdded varKey
    addFixpEq upperEqMap varKey pushEq
    addFixpEq lowerEqMap varKey pushEq
    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
            => VarMap
            -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
            -> (AST -> AST -> Z3 AST)
            -> GraphNode state
            -> VarKey
            -> AST
            -> Bool
            -> Z3 [(Int, Int)]
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
      --DBG.traceM $ "Asserting Shift equation: " ++ eqString
      assert eq
      assert =<< mkGe var =<< mkRealNum (0 :: Rational)

    --DBG.traceM $ show varKey ++ " = ShiftEq " ++ show terms
    let shiftEq | null terms = error "shift semiconfs should go somewhere!"
                | otherwise = ShiftEq terms
    addFixpEq upperEqMap varKey shiftEq
    addFixpEq lowerEqMap varKey shiftEq
    return unencoded_vars
-- end

---------------------------------------------------------------------------------------------------
-- compute the exact termination probabilities, but do it with a backward analysis for every SCC --
---------------------------------------------------------------------------------------------------

type SuccessorsPopContexts = IntSet

type PartialVarMap = (HT.BasicHashTable VarKey AST, Bool)

data DeficientGlobals state = DeficientGlobals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , successorsCntxs :: MV.IOVector SuccessorsPopContexts
  , mustReachPop :: IORef IntSet
  , cannotReachPop :: IORef IntSet
  , partialVarMap :: PartialVarMap
  , rewVarMap :: RewVarMap
  , upperEqMap :: EqMap EqMapNumbersType
  , lowerEqMap :: EqMap EqMapNumbersType
  , eps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

-- requires: the initial semiconfiguration is at position 0 in the Support graph
terminationQuerySCC :: (Eq state, Hashable state, Show state)
                 => SupportGraph state
                 -> EncPrecFunc
                 -> TermQuery
                 -> STRef RealWorld Stats
                 -> Z3 (TermResult, IntSet)
terminationQuerySCC suppGraph precFun query oldStats = do
  newSS              <- liftIO ZS.new
  newBS              <- liftIO ZS.new
  newIVec            <- liftIO $ MV.replicate (V.length suppGraph) 0
  newSuccessorsCntxs <- liftIO $ MV.replicate (V.length suppGraph) IntSet.empty
  emptyCannotReachPop <- liftIO $ newIORef IntSet.empty
  newMap <- liftIO HT.new
  newUpperEqMap <- liftIO HT.new
  newLowerEqMap <- liftIO HT.new
  emptyMustReachPop <- liftIO $ newIORef IntSet.empty
  newRewVarMap <- liftIO HT.new
  newEps <- liftIO $ newIORef defaultEps
  let globals = DeficientGlobals { sStack = newSS
                                , bStack = newBS
                                , iVector = newIVec
                                , successorsCntxs = newSuccessorsCntxs
                                , mustReachPop = emptyMustReachPop
                                , cannotReachPop = emptyCannotReachPop
                                , partialVarMap = (newMap, encodeInitialSemiconf query)
                                , rewVarMap = newRewVarMap
                                , upperEqMap = newUpperEqMap
                                , lowerEqMap = newLowerEqMap
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
  unless (IntSet.null popCntx) $ error "the initial state cannot reach any pop"

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
        lowerProbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, d)) <$> liftIO (HT.toList newLowerEqMap)
        let lowerProbRationalMap = GeneralMap.map (\v -> approxRational (v - actualEps) actualEps) lowerProbMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery SMTWithHints) = do
        ub <- if isAST then return 1 else extractUpperProb . fromJust =<< liftIO (HT.lookup newMap (0,-1))
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newLowerEqMap (0,-1))
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound SMTWithHints) = do
        ub <- if isAST then return 1 else extractUpperProb . fromJust =<< liftIO (HT.lookup newMap (0,-1))
        DBG.traceM $ "Computed upper bound: " ++ show ub
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newLowerEqMap (0,-1))
        DBG.traceM $ "Computed lower bound: " ++ show lb
        DBG.traceM $ "Comparing: " ++ show comp ++ " " ++ show bound
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)
      readResults (ApproxAllQuery ExactSMTWithHints) = readResults (ApproxAllQuery SMTWithHints)
      readResults (ApproxSingleQuery ExactSMTWithHints) = readResults (ApproxSingleQuery SMTWithHints)
      readResults (CompQuery comp bound ExactSMTWithHints) = readResults (CompQuery comp bound SMTWithHints)
      readResults (ApproxAllQuery OVI) = do
        upperProbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, d)) <$> liftIO (HT.toList newUpperEqMap)
        let upperProbRationalMap = GeneralMap.map (\v -> approxRational (v + actualEps) actualEps) upperProbMap
        lowerProbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, d)) <$> liftIO (HT.toList newLowerEqMap)
        let lowerProbRationalMap = GeneralMap.map (\v -> approxRational (v - actualEps) actualEps) lowerProbMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery OVI) = do
        ub <- if isAST then return 1 else (\(PopEq d) -> approxRational (d + actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newUpperEqMap (0,-1))
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newLowerEqMap (0,-1))
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound OVI) = do
        ub <- if isAST then return 1 else (\(PopEq d) -> approxRational (d + actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newUpperEqMap (0,-1))
        lb <- if isAST then return 1 else (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newLowerEqMap (0,-1))
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)
  readResults query

dfs :: (Eq state, Hashable state, Show state)
    => SupportGraph state
    -> DeficientGlobals state
    -> EncPrecFunc
    -> (Bool, Bool)
    -> GraphNode state
    -> Z3 (SuccessorsPopContexts, Bool)
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
addtoPath :: DeficientGlobals state -> GraphNode state -> Z3 ()
addtoPath globals gn = liftIO $ do
  ZS.push (sStack globals) (gnId gn)
  sSize <- ZS.size $ sStack globals
  MV.unsafeWrite (iVector globals) (gnId gn) sSize
  ZS.push (bStack globals) sSize

merge ::  DeficientGlobals state -> GraphNode state -> Z3 ()
merge globals gn = liftIO $ do
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  ZS.popWhile_ (bStack globals) (iVal <)

createComponent :: (Eq state, Hashable state, Show state)
                => SupportGraph state
                -> DeficientGlobals state
                -> GraphNode state
                -> (SuccessorsPopContexts, Bool)
                -> EncPrecFunc
                -> (Bool,  Bool)
                -> Z3 (SuccessorsPopContexts, Bool)
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
        DBG.traceM  $ "Popped Semiconfigurations: " ++ show poppedEdges
        DBG.traceM $ "Pop contexts: " ++ show popContxs
        DBG.traceM  $ "Length of current SCC: " ++ show (length poppedEdges)
        forM_ poppedEdges $ \e -> do
          liftIO $ MV.unsafeWrite (iVector globals) e (-1)
          liftIO $ MV.unsafeWrite (successorsCntxs globals) e popContxs
        return poppedEdges
      doEncode poppedEdges  = do
        newAdded <- liftIO HT.new
        let toEncode = [(gnId_, rc) | gnId_ <- poppedEdges, rc <- IntSet.toList popContxs]
            sccMembers = IntSet.fromList poppedEdges
        insertedVars <- map (snd . fromJust) <$> forM toEncode (lookupVar (varMap, newAdded, sccMembers, encodeInitial) (lEqMap, uEqMap))
        when (or insertedVars ) $ error "inserting a variable that has already been encoded"
        -- delete previous assertions and encoding the new ones
        reset >> encode toEncode (varMap, newAdded, sccMembers, encodeInitial) (lowerEqMap globals, upperEqMap globals) suppGraph precFun mkComp useZ3
        actualMustReachPop <- solveSCCQuery suppGraph dMustReachPop (varMap, newAdded, sccMembers, encodeInitial) globals precFun (useZ3, exactEq)
        when actualMustReachPop $ forM_ poppedEdges $ \e -> liftIO $ modifyIORef' (mustReachPop globals) $ IntSet.insert e
        return (popContxs, actualMustReachPop)
      doNotEncode poppedEdges = do
        liftIO $ modifyIORef' (cannotReachPop globals) $ IntSet.union (IntSet.fromList poppedEdges)
        if gnId gn == 0 && encodeInitial
          then do -- for the initial semiconf, encode anyway
            newAdded <- liftIO HT.new
            var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
            liftIO $ HT.insert varMap (0, -1) var
            liftIO $ HT.insert newAdded (0, -1) var
            reset >> encode [(0, -1)] (varMap, newAdded, IntSet.singleton 0, encodeInitial) (lowerEqMap globals, upperEqMap globals) suppGraph precFun mkComp useZ3
            actualMustReachPop <- solveSCCQuery suppGraph dMustReachPop (varMap, newAdded, IntSet.singleton 0, encodeInitial)  globals precFun (useZ3, exactEq)
            return (popContxs, actualMustReachPop)
          else return (popContxs, False)
      cases
        | iVal /= topB = return (popContxs, dMustReachPop)
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases

-- params:
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveSCCQuery :: (Eq state, Hashable state, Show state)
              => SupportGraph state -> Bool -> VarMap -> DeficientGlobals state -> EncPrecFunc -> (Bool, Bool) -> Z3 Bool
solveSCCQuery suppGraph dMustReachPop varMap@(m, newAdded, sccMembers, _) globals precFun (useZ3, exactEq) = do
  liftIO $ stToIO $ modifySTRef' (stats globals) $ \s@Stats{sccCount = acc} -> s{sccCount = acc + 1}
  liftIO $ stToIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCount = acc} -> s{largestSCCSemiconfsCount = max acc (IntSet.size sccMembers)}
  variables <- liftIO $ map fst <$> HT.toList newAdded
  DBG.traceM $ "New variables of this SCC: " ++ show variables
  currentEps <- liftIO $ readIORef (eps globals)

  let lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals
      rVarMap = rewVarMap globals
      augTolerance = 100 * defaultTolerance
      cases unsolvedVars
        | null unsolvedVars = DBG.traceM "No equation system has to be solved here, just propagated all the values."
        | useZ3 = do
            updateLowerBound unsolvedVars
            updateUpperBoundsZ3 unsolvedVars
        | otherwise = do
          updateLowerBound unsolvedVars
          updateUpperBoundsOVI unsolvedVars
      updateLowerBound unsolvedVars = do
        -- updating lower bounds
        liftIO $ stToIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquations = acc} -> s{nonTrivialEquations = acc + length unsolvedVars}
        approxVec <- approxFixpWithHints lEqMap defaultEps defaultMaxIters unsolvedVars
        forM_ unsolvedVars $ \varKey -> do
          liftIO (HT.lookup lEqMap varKey) >>= \case
              Just (PopEq _) -> error "trying to update a variable that is already dead"
              _ -> do
                p <- liftIO $ fromJust <$> HT.lookup approxVec varKey
                addFixpEq lEqMap varKey (PopEq p)
      --         
      doAssert approxFracVec currentEps = do
        push -- create a backtracking point
        epsReal <- mkRealNum currentEps

        forM_ approxFracVec (\(varKey, pRational) -> liftIO (HT.lookup uEqMap varKey) >>= \case
          Just (PopEq _) -> error "trying to update a variable that is already dead"
          _ -> do
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
                DBG.traceM $ "Unsat, backtrack. Current eps: " ++ show currentEps
                liftIO (writeIORef (eps globals) (2 * currentEps)) >> pop 1 >> doAssert approxFracVec (2 * currentEps) -- backtrack one point and restart
            | otherwise -> error "Maximum tolerance reached when solving SCC"
          _ -> error "Undefinite result when checking an SCC"
      --
      updateUpperBoundsZ3 unsolvedVars = do
        startUpper <- startTimer
        DBG.traceM "Approximating via Value Iteration + z3"
        approxVec <- approxFixpWithHints uEqMap defaultEps defaultMaxIters unsolvedVars
        approxFracVec <- toRationalProbVecWithHints defaultEps approxVec unsolvedVars

        DBG.traceM "Asserting lower and upper bounds computed from value iteration, and getting a model"
        model <- doAssert approxFracVec (min defaultTolerance currentEps)

        -- actual updates
        augUnsolvedVars <- liftIO $ mapM (\k -> (k,) . fromJust <$> HT.lookup newAdded k) unsolvedVars
        forM_ augUnsolvedVars $ \(varKey, varAST) -> do
          ubAST <- fromJust <$> eval model varAST
          liftIO $ HT.insert m varKey ubAST

        upperBound <- foldM (\acc (varKey, varAST) -> do
          liftIO (HT.lookup uEqMap varKey) >>= \case
              Just (PopEq _) -> error "trying to update a variable that is already dead"
              _ -> do
                pDouble <- extractUpperDouble . fromJust =<< eval model varAST
                addFixpEq uEqMap varKey (PopEq pDouble)
                return ((varKey, pDouble):acc))
          [] augUnsolvedVars
        tUpper <- stopTimer startUpper $ null upperBound
        liftIO $ stToIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
      --
      updateUpperBoundsOVI unsolvedVars = do
        startUpper <- startTimer
        DBG.traceM "Using OVI to update upper bounds"
        oviRes <- oviWithHints defaultOVISettingsDouble uEqMap unsolvedVars
        rCertified <- oviToRationalWithHints defaultOVISettingsDouble uEqMap oviRes unsolvedVars
        unless rCertified $ error "cannot deduce a rational certificate for this semiconf"
        unless (oviSuccess oviRes || rCertified) $ error "OVI was not successful in computing an upper bound on the termination probabilities"

        -- actual updates
        forM_ unsolvedVars $ \varKey -> do
          ub <- liftIO $ min (1 :: Double) . fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
          ubAST <- mkRealNum ub
          liftIO $ HT.insert m varKey ubAST

        upperBound <- foldM (\acc varKey -> do
          liftIO (HT.lookup uEqMap varKey) >>= \case
              Just (PopEq _) -> error "trying to update a variable that is already dead"
              _ -> do
                p <- liftIO $ fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
                addFixpEq uEqMap varKey (PopEq p)
                return ((varKey, p): acc))
          [] unsolvedVars

        tUpper <- stopTimer startUpper $ null upperBound
        liftIO $ stToIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })

  -- preprocessing phase
  _ <- preprocessApproxFixpWithHints lEqMap defaultEps (3 * IntSet.size sccMembers) variables
  (updatedUpperVars, unsolvedVars) <- preprocessApproxFixpWithHints uEqMap defaultEps (3 * IntSet.size sccMembers) variables
  forM_ updatedUpperVars $ \(varKey, p) -> do
    pAST <- mkRealNum (p :: Double)
    liftIO $ HT.insert m varKey pAST

  -- lEqMap and uEqMap should be the same here
  DBG.traceM $ "Number of live equations to be solved: " ++ show (length unsolvedVars) ++ " - unsolved variables: " ++ show unsolvedVars
  liftIO $ stToIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCEqsCount = acc } -> s{ largestSCCEqsCount = max acc (length unsolvedVars) }

  -- find bounds for this SCC
  cases unsolvedVars
  upperBound <- liftIO $ forM variables $ \k -> do PopEq u <- fromJust <$> HT.lookup uEqMap k; return (k,u)
  let upperBoundsTermProbs = Map.fromListWith (+) . map (\(key, ub) -> (fst key, ub)) $ upperBound
  let upperBounds = GeneralMap.fromList upperBound
  DBG.traceM $ "Computed upper bounds: " ++ show upperBounds
  DBG.traceM $ "Computed upper bounds on termination probabilities: " ++ show upperBoundsTermProbs
  DBG.traceM $ "Do all the descendant terminate almost surely? " ++ show dMustReachPop
  DBG.traceM $ "Are the upper bounds proving not AST? " ++ show (all (\(_,ub) -> ub < 1 - defaultTolerance) (Map.toList upperBoundsTermProbs))

  -- computing the PAST certificate (if needed)
  let nonASTprobs = all (\(_,ub) -> ub < 1 - augTolerance) (Map.toList upperBoundsTermProbs)
      aSTprobs = all (\(_,ub) -> ub > 1 - augTolerance) (Map.toList upperBoundsTermProbs)
      pASTCertCases
        | not dMustReachPop && not nonASTprobs = error "Descendants are not PAST but this SCC has termination upper bound equal to 1"
        | nonASTprobs = DBG.traceM "The upper bound is enough to prove non AST" >> return False
        | null unsolvedVars || exactEq = return True
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
            (Unsat, _) -> do
              unless nonASTprobs $ error "fail to prove PAST when some semiconfs have upper bounds on their termination equal to 1"
              DBG.traceM "PAST certification failed!" >> return False
            (Sat, _) -> do
              unless aSTprobs $ error "Found a PAST certificate for non AST SCC!!"
              DBG.traceM "PAST certification succeeded!" >> return True
            _ -> error "undefined result when running the PAST certificate"

          tPast <- stopTimer startPast pastRes
          liftIO $ stToIO $ modifySTRef' (stats globals) (\s -> s { pastTime = pastTime s + tPast })
          return pastRes
  pASTCertCases

--- REWARDS COMPUTATION for certificating PAST  ---------------------------------
type RewVarKey = Int
type RewVarMap = HT.BasicHashTable Int AST

-- (Z3 Var, was it already present?)
lookupRewVar :: RewVarMap -> RewVarKey -> Z3 (AST, Bool)
lookupRewVar rewVarMap key = do
  maybeVar <- liftIO $ HT.lookup rewVarMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      newVar <- mkFreshRealVar $ show key
      liftIO $ HT.insert rewVarMap key newVar
      return (newVar, False)
-- end helpers


encodeReward :: (Eq state, Hashable state, Show state)
      => [RewVarKey]
      -> VarMap
      -> RewVarMap
      -> SupportGraph state
      -> EncPrecFunc
      -> (AST -> AST -> Z3 AST)
      -> Z3 ()
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
encodeRewPush :: (Eq state, Hashable state, Show state)
           => SupportGraph state
           -> VarMap
           -> RewVarMap
           -> (AST -> AST -> Z3 AST)
           -> GraphNode state
           -> AST
           -> Z3 [RewVarKey]
encodeRewPush graph (m, _, _ ,_) rewVarMap mkComp gn var =
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

encodeRewShift :: (Eq state, Hashable state, Show state)
  => RewVarMap
  -> (AST -> AST -> Z3 AST)
  -> GraphNode state
  -> AST
  -> Z3 [RewVarKey]
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
