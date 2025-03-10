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
import Data.Bifunctor(first)

import Z3.Monad
import Data.IORef (IORef, newIORef, modifyIORef', readIORef, writeIORef)

import Data.STRef (STRef, modifySTRef')
import qualified Pomc.IOMapMap as MM
-- import qualified Debug.Trace as DBG

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = HT.BasicHashTable VarKey AST

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
-- end helpers

encode :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
       => [(Int, Int)]
       -> VarMap
       -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
       -> SupportGraph state
       -> EncPrecFunc
       -> (AST -> AST -> z3 AST)
       -> Bool
       -> IntSet
       -> Int
       -> z3 Int
encode [] _ _ _ _ _ _ _ count = return count
encode ((gnId_, rightContext):unencoded) tVarMap eqs graph precFun mkComp useZ3 sccMembers count = do
  let varKey = (gnId_, rightContext)
  var <- liftIO $ fromJust <$> HT.lookup tVarMap varKey
  let gn = graph ! gnId_
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        | precRel == Just Yield =
            encodePush graph tVarMap eqs mkComp gn varKey var useZ3 sccMembers

        | precRel == Just Equal =
            encodeShift tVarMap eqs mkComp gn varKey var useZ3 sccMembers

        | precRel == Just Take = do
            let e = Map.findWithDefault 0 rightContext (popContexts gn)
            when useZ3 $ do
              solvedVar <- mkRealNum e
              liftIO $ HT.insert tVarMap varKey solvedVar

            addFixpEq eqs varKey $ PopEq (fromRational e, fromRational e)
            return [] -- pop transitions do not generate new variables

        | otherwise = fail "unexpected prec rel"
  newUnencoded <- cases
  encode (newUnencoded ++ unencoded) tVarMap eqs graph precFun mkComp useZ3 sccMembers (count + 1)

-- encoding helpers --
retrieveInitialPush :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
           => EqMapNumbersType
           -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
           -> GraphNode state
           -> z3 (Prob, Prob)
retrieveInitialPush eps eqs gn = let
  foldUBs prob_ pushEqs = (fromRational prob_) * sum (map (\(_, PopEq (_, n)) -> n) pushEqs)
  foldLBs prob_ pushEqs = (fromRational prob_) * sum (map (\(_, PopEq (n, _)) -> n) pushEqs)
  updateLB e pushEqs accLB = (accLB + foldLBs (prob e) pushEqs)
  updateUB e pushEqs accUB = (accUB + foldUBs (prob e) pushEqs)
  toRationalLB b = approxRational (b - eps) eps
  toRationalUB b = approxRational (b + eps) eps
  in do
    logDebugN $ "Transitions of initial push: " ++ show (Set.toList $ internalEdges gn)
    (lb, ub) <- foldM (\(accLB, accUB) e -> do
      pushEqs <- retrieveEquations eqs (to e)
      let newAccUB = updateUB e pushEqs accUB
          newAccLB = updateLB e pushEqs accLB
      return (newAccLB, newAccUB)
      ) (0, 0) (Set.toList $ internalEdges gn)
    return (toRationalLB lb, toRationalUB ub)

-- encoding helpers --
encodePush :: (MonadZ3 z3, Eq state, Hashable state, Show state)
           => SupportGraph state
           -> VarMap
           -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
           -> (AST -> AST -> z3 AST)
           -> GraphNode state
           -> VarKey
           -> AST
           -> Bool
           -> IntSet
           -> z3 [(Int, Int)]
encodePush graph varMap eqs mkComp  gn varKey@(_, rightContext) var useZ3 sccMembers =
  let pushSemiconfs = Set.toList $ Set.map (\e -> (gnId $ graph ! to e, prob e)) (internalEdges gn)
      suppSemiconfs = Set.toList $ Set.map (\e -> graph ! to e) (supportEdges gn)
      suppEndsIds = map (getId . fst . semiconf) suppSemiconfs
      suppInfo = zip suppEndsIds (map (\gn -> (gnId gn, rightContext)) suppSemiconfs)
      pushSemiconfswithSuppIds = [((p, rc), prob_) | (p,prob_) <- pushSemiconfs, rc <- suppEndsIds]
  in do
    newUnencoded <- liftIO $ newIORef []
    suppVarKeys  <- foldM (\acc (sId, varKey) -> do
        maybeVar <- liftIO $ HT.lookup varMap varKey
        let cases
              | isJust maybeVar = return $ (fromJust maybeVar, sId, varKey):acc
              | IntSet.notMember (fst varKey) sccMembers = return acc
              | otherwise = do -- we might discover new variables
                  var <- mkFreshRealVar $ show varKey
                  liftIO $ HT.insert varMap varKey var
                  liftIO $ modifyIORef' newUnencoded $ \x -> varKey:x
                  return $ (var, sId, varKey):acc
        cases
      ) [] suppInfo

    pushVarKeys <- foldM (\acc (varKey, prob_) -> do
      maybeVar <- liftIO $ HT.lookup varMap varKey
      let rc = snd varKey
          cases
            | isJust maybeVar = return $ (fromJust maybeVar, prob_, rc, varKey):acc
            | IntSet.notMember (fst varKey) sccMembers = return acc
            | otherwise = do -- we might discover new variables
                newVar <- mkFreshRealVar $ show varKey
                liftIO $ HT.insert varMap varKey newVar
                liftIO $ modifyIORef' newUnencoded $ \x -> varKey:x
                return $ (newVar, prob_, rc, varKey):acc
      cases
      ) [] pushSemiconfswithSuppIds

    let terms = [(prob_, pushTerm, suppVarKey) |
                  (_, suppSId, suppVarKey) <- suppVarKeys,
                  (_, prob_, rc, pushTerm) <- pushVarKeys,
                  rc == suppSId
                ]
        z3Terms = [(prob_, pushTerm, suppVarKey) |
                    (suppVarKey, suppSId, _) <- suppVarKeys,
                    (pushTerm, prob_, rc, _) <- pushVarKeys,
                    rc == suppSId
                  ]
        emptyPush = null terms
        pushEq | emptyPush = PopEq (0, 0)
               | otherwise = PushEq terms
        encodePush (prob_, pushTerm, suppVarKey) = do
            probReal <- mkRealNum prob_
            mkMul [probReal, pushTerm, suppVarKey]

    when useZ3 $ if emptyPush
        then do
          solvedVar <- mkRealNum (0 :: Rational)
          liftIO $ HT.insert varMap varKey solvedVar
          assert =<< mkEq var solvedVar
        else do
          assert =<< mkComp var =<< mkAdd1 =<< mapM encodePush z3Terms

    addFixpEq eqs varKey pushEq
    liftIO $ readIORef newUnencoded

encodeShift :: (MonadZ3 z3, Eq state, Hashable state, Show state)
            => VarMap
            -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
            -> (AST -> AST -> z3 AST)
            -> GraphNode state
            -> VarKey
            -> AST
            -> Bool
            -> IntSet
            -> z3 [(Int, Int)]
encodeShift varMap eqs mkComp gn varKey@(_, rightContext) var useZ3 sccMembers =
  let shiftEnc (currs, newVars, terms) e = do
        let toKey = (to e, rightContext)
        maybeVar <- liftIO $ HT.lookup varMap toKey
        let toVar = fromJust maybeVar
            prob_ = prob e
            cases
              | isJust maybeVar = do
                trans <- encodeTransition e toVar
                return (trans:currs, newVars, (prob_, toKey):terms)
              | IntSet.notMember (fst toKey) sccMembers = return (currs, newVars, terms)
              | otherwise = do -- it might happen that we discover new variables
                  newVar <- mkFreshRealVar $ show toKey
                  liftIO $ HT.insert varMap toKey newVar
                  trans <- encodeTransition e newVar
                  return (trans:currs, toKey:newVars, (prob_, toKey):terms)
        cases

  in do
    (transitions, unencodedVars, terms) <- foldM shiftEnc ([], [], []) (internalEdges gn)
    when useZ3 $ assert =<< mkComp var =<< mkAdd1 transitions

    -- logDebugN $ show varKey ++ " = ShiftEq " ++ show terms
    addFixpEq eqs varKey (ShiftEq terms)
    return unencodedVars

---------------------------------------------------------------------------------------------------
-- compute termination probabilities, but do it with a backward analysis for every SCC --
---------------------------------------------------------------------------------------------------

type SuccessorsPopContexts = IntSet

data DeficientGlobals state = DeficientGlobals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , successorsCntxs :: MV.IOVector SuccessorsPopContexts
  , mustReachPop :: IORef IntSet
  , varMap :: VarMap
  , rewVarMap :: RewVarMap
  , eqMap :: AugEqMap (EqMapNumbersType, EqMapNumbersType)
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
  newEqMap <- liftIO MM.empty
  newLiveVars <- liftIO $ newIORef Set.empty
  emptyMustReachPop <- liftIO $ newIORef IntSet.empty
  newRewVarMap <- liftIO HT.new
  newEps <- liftIO $ newIORef defaultEps
  let globals = DeficientGlobals { sStack = newSS
                                , bStack = newBS
                                , iVector = newIVec
                                , successorsCntxs = newSuccessorsCntxs
                                , mustReachPop = emptyMustReachPop
                                , varMap = newMap
                                , rewVarMap = newRewVarMap
                                , eqMap = (newEqMap, newLiveVars)
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
  (_, isAST) <- dfs suppGraph globals precFun (useZ3, exactEq) gn
  logInfoN $ "Is AST: " ++ show isAST

  -- returning the computed values
  currentEps <- liftIO $ readIORef (eps globals)
  mustReachPopIdxs <- liftIO $ readIORef (mustReachPop globals)
  let actualEps = min defaultEps $ currentEps * currentEps
      intervalLogic (_, ub) Lt p = ub < p
      intervalLogic (lb, _) Gt p = lb > p
      intervalLogic (_, ub) Le p = ub <= p
      intervalLogic (lb, _) Ge p = lb >= p
      approxL (v, _) = approxRational (v - actualEps) actualEps
      approxU (_, v) = approxRational (v + actualEps) actualEps
      unlessAST f = if isAST then return (1,1) else f
      readResults (ApproxAllQuery SMTWithHints) = do
        upperProbRationalMap <- GeneralMap.fromList <$> (mapM (\(varKey, varAST) -> do
            pRational <- extractUpperProb varAST
            return (varKey, pRational)) =<< liftIO (HT.toList newMap))
        probMap <- liftIO $ GeneralMap.map (\(PopEq d) -> d) <$> MM.foldMaps newEqMap
        let lowerProbRationalMap = GeneralMap.map approxL probMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery SMTWithHints) = do
        (lb, ub) <- unlessAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound SMTWithHints) = do
        (lb, ub) <- unlessAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)
      readResults (ApproxAllQuery ExactSMTWithHints) = readResults (ApproxAllQuery SMTWithHints)
      readResults (ApproxSingleQuery ExactSMTWithHints) = readResults (ApproxSingleQuery SMTWithHints)
      readResults (CompQuery comp bound ExactSMTWithHints) = readResults (CompQuery comp bound SMTWithHints)
      readResults (ApproxAllQuery OVI) = liftIO $ do
        probMap <- GeneralMap.map (\(PopEq d) -> d) <$> MM.foldMaps newEqMap
        let upperProbRationalMap = GeneralMap.map approxU probMap
        let lowerProbRationalMap = GeneralMap.map approxL probMap
        return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
      readResults (ApproxSingleQuery OVI) = do
        (lb, ub) <- unlessAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (ApproxSingleResult (lb, ub), mustReachPopIdxs)
      readResults (CompQuery comp bound OVI) = do
        (lb, ub) <- unlessAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (toTermResult $ intervalLogic (lb,ub) comp bound, mustReachPopIdxs)

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
  let tVarMap = varMap globals
      eqs = eqMap globals
      mkComp = (if exactEq then mkEq else mkGe)
      createC = do
        liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCount = acc} -> s{sccCount = acc + 1}
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
        forM_ toEncode $ \key -> do
          var <- mkFreshRealVar $ show key
          liftIO $ HT.insert tVarMap key var
        -- delete previous assertions and encoding the new ones
        reset
        eqsCount <- encode toEncode tVarMap eqs suppGraph precFun mkComp useZ3 sccMembers 0
        liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCount = acc} -> s{ equationsCount = acc + eqsCount}
        logDebugN $ "Must reach pop of descendant: " ++ show dMustReachPop
        actualMustReachPop <- solveSCCQuery suppGraph dMustReachPop tVarMap globals precFun (useZ3, exactEq) sccMembers
        when actualMustReachPop $ forM_ poppedEdges $ \e -> liftIO $ modifyIORef' (mustReachPop globals) $ IntSet.insert e
        return (popContxs, actualMustReachPop)
      cases
        | iVal /= topB = return (popContxs, dMustReachPop)
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | gnId gn == 0 = return (popContxs, dMustReachPop) -- cannot reach a pop
        | otherwise = createC >> return (popContxs, False) 
  cases

-- params:
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveSCCQuery :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Eq state, Hashable state, Show state)
              => SupportGraph state -> Bool -> VarMap -> DeficientGlobals state -> EncPrecFunc -> (Bool, Bool) -> IntSet -> z3 Bool
solveSCCQuery suppGraph dMustReachPop tVarMap globals precFun (useZ3, exactEq) sccMembers = do
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCount = acc} -> s{sccCount = acc + 1}
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCount = acc} -> s{largestSCCSemiconfsCount = max acc (IntSet.size sccMembers)}
  --logDebugN $ "New variables of this SCC: " ++ show variables
  currentEps <- liftIO $ readIORef (eps globals)

  let eqs = eqMap globals
      rVarMap = rewVarMap globals
      augTolerance = 100 * defaultTolerance
      sccLen = IntSet.size sccMembers
      cases unsolvedVars
        | null unsolvedVars = logDebugN "No equation system has to be solved here, just propagated all the values." >> return []
        | useZ3 = updateLowerBound >>= updateUpperBoundsZ3
        | otherwise = updateLowerBound >>= updateUpperBoundsOVI
      updateLowerBound = approxFixp eqs fst defaultEps defaultMaxIters
      --
      doAssert approxFracVec currentEps = do
        push -- create a backtracking point
        epsReal <- mkRealNum currentEps

        V.forM_ approxFracVec (\(varKey, pRational) -> do
            var <- liftIO $ fromJust <$> HT.lookup tVarMap varKey
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
      updateUpperBoundsZ3 lowerBound = do
        startUpper <- startTimer
        logDebugN "Approximating via Value Iteration + z3"
        approxVec <- approxFixp eqs snd defaultEps defaultMaxIters
        let approxFracVec = toRationalProbVec defaultEps approxVec
        logDebugN "Asserting lower and upper bounds computed from value iteration, and getting a model"
        varKeys <- liveVariables eqs
        model <- doAssert (V.zip varKeys approxFracVec) (min defaultTolerance currentEps)

        -- actual updates
        upperBound <- foldM (\acc (varKey, l) -> do
          varAST <- liftIO $ fromJust <$> HT.lookup tVarMap varKey
          ubAST <- fromJust <$> eval model varAST
          pDouble <- extractUpperDouble ubAST
          liftIO $ HT.insert tVarMap varKey ubAST
          addFixpEq eqs varKey (PopEq (l, pDouble))
          return ((varKey, pDouble):acc)
          ) [] (V.zip varKeys lowerBound)

        tUpper <- stopTimer startUpper upperBound
        liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
        return upperBound
      --
      updateUpperBoundsOVI lowerBound = do
        startUpper <- startTimer
        logDebugN "Using OVI to update upper bounds"
        oviRes <- ovi defaultOVISettingsDouble eqs snd
        rCertified <- oviToRational defaultOVISettingsDouble eqs snd oviRes
        unless rCertified $ error "cannot deduce a rational certificate for this semiconf"
        unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bound on the termination probabilities"

        -- actual updates
        varKeys <- liveVariables eqs
        let bounds = V.zip3 varKeys lowerBound (oviUpperBound oviRes)
        upperBoundWithKeys <- V.mapM ( \(varKey, l, p) -> do
          let ub = min (1 :: Double) p
          ubAST <- mkRealNum ub
          liftIO $ HT.insert tVarMap varKey ubAST
          addFixpEq eqs varKey (PopEq (l,p))
          return (varKey, p)
          ) bounds
        tUpper <- stopTimer startUpper True
        liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
        return $ V.toList upperBoundWithKeys

  -- preprocessing phase
  -- preprocessing to solve variables that do not need ovi
  zeroVars <- preprocessZeroApproxFixp eqs fst defaultEps (sccLen + 1)
  forM_ zeroVars $ \(k, v) -> do
    pAST <- mkRealNum (v :: Double)
    liftIO $ HT.insert tVarMap k pAST
    addFixpEq eqs k (PopEq (v, v))

  (solvedLVars, _) <- preprocessApproxFixp eqs fst
  (solvedUvars, unsolvedVars) <- preprocessApproxFixp eqs snd

  let zipSolved = zip solvedLVars solvedUvars
  forM_ zipSolved $ \((varKey, l), (_, u)) -> do
    pAST <- mkRealNum (u :: Double)
    liftIO $ HT.insert tVarMap varKey pAST
    addFixpEq eqs varKey (PopEq (l,u))

  -- lEqMap and uEqMap have the same unsolved equations
  logDebugN $ "Number of live equations to be solved: " ++ show (length unsolvedVars) ++ " - unsolved variables: " ++ show unsolvedVars
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCNonTrivialEqsCount = acc } -> s{ largestSCCNonTrivialEqsCount = max acc (length unsolvedVars) }
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquationsCount = acc} -> s{nonTrivialEquationsCount = acc + length unsolvedVars}


  -- find bounds for this SCC
  upperBound <- cases unsolvedVars
  let upperBoundsTermProbs = Map.toList . Map.fromListWith (+) . map (first fst) $ (upperBound ++ solvedUvars)
  let upperBounds = GeneralMap.fromList upperBound
  logDebugN $ unlines
    [ "Computed upper bounds: " ++ show upperBounds
    , "Computed upper bounds on termination probabilities: " ++ show upperBoundsTermProbs
    , "Do all the descendant terminate almost surely? " ++ show dMustReachPop
    , "Are the upper bounds proving not AST? " ++ show (all (\(_,ub) -> ub < 1 - defaultTolerance) upperBoundsTermProbs)
    ]

  -- computing the PAST certificate (if needed)
  let nonASTprobs = all (\(_,ub) -> ub < 1 - augTolerance) upperBoundsTermProbs
      aSTprobs = all (\(_,ub) -> ub > 1 - augTolerance) upperBoundsTermProbs
      exactASTprobs = all (\(_,ub) -> ub > 1 - defaultTolerance) upperBoundsTermProbs
      pASTCertCases
        | null unsolvedVars = return dMustReachPop -- just propagating
        | exactEq = return exactASTprobs
        | not dMustReachPop && aSTprobs =
          error $ "Descendants are not PAST but these semiconfs have termination upper bounds equal to 1: " ++ show upperBoundsTermProbs
        | nonASTprobs = logDebugN "The upper bound is enough to prove non AST" >> return False
        | otherwise = do
          startPast <- startTimer
          forM_ (IntSet.toList sccMembers) $ \k -> do
              (_, alreadyEnc) <- lookupRewVar rVarMap k
              when alreadyEnc $ error "encoding a variable for a semiconf that has already been encoded"
          reset >> encodeReward (IntSet.toList sccMembers) tVarMap rVarMap suppGraph precFun mkGe
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
lookupRewVar rVarMap key = do
  maybeVar <- liftIO $ HT.lookup rVarMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      newVar <- mkFreshRealVar $ show key
      liftIO $ HT.insert rVarMap key newVar
      return (newVar, False)

encodeReward :: (MonadZ3 z3, MonadFail z3, Eq state, Hashable state, Show state)
             => [RewVarKey]
             -> VarMap
             -> RewVarMap
             -> SupportGraph state
             -> EncPrecFunc
             -> (AST -> AST -> z3 AST)
             -> z3 ()
encodeReward [] _ _ _ _ _ = return ()
encodeReward (gnId_:unencoded) tVarMap rVarMap graph precFun mkComp = do
  rewVar <- liftIO $ fromJust <$> HT.lookup rVarMap gnId_
  let gn = graph ! gnId_
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel
      cases
        | precRel == Just Yield =
          encodeRewPush graph tVarMap rVarMap mkComp gn rewVar

        | precRel == Just Equal =
            encodeRewShift rVarMap mkComp gn rewVar

        | precRel == Just Take = do
            assert =<< mkEq rewVar =<< mkRealNum (1 :: Prob)
            return []

        | otherwise = fail "unexpected prec rel"

  newUnencoded <- cases
  encodeReward (newUnencoded ++ unencoded) tVarMap rVarMap graph precFun mkComp

-- encoding helpers --
encodeRewPush :: (MonadZ3 z3, Eq state, Hashable state, Show state)
              => SupportGraph state
              -> VarMap
              -> RewVarMap
              -> (AST -> AST -> z3 AST)
              -> GraphNode state
              -> AST
              -> z3 [RewVarKey]
encodeRewPush graph m rVarMap mkComp gn var =
  let closeSummaries pushGn (currs, unencodedVars) e = do
        let supportGn = graph ! (to e)
        maybeTermProb <- liftIO $ HT.lookup m (gnId pushGn, getId . fst . semiconf $ supportGn)
        if isNothing maybeTermProb
          then return (currs, unencodedVars)
          else do
            (summaryVar, alreadyEncoded) <- lookupRewVar rVarMap (gnId supportGn)
            eq <- mkMul [fromJust maybeTermProb, summaryVar]
            return ( eq:currs
                  ,  if alreadyEncoded then unencodedVars else (gnId supportGn):unencodedVars
                  )
      pushEnc (currs, vars) e = do
        let pushGn = graph ! (to e)
        (pushVar, alreadyEncoded) <- lookupRewVar rVarMap (gnId pushGn)
        (equations, unencodedVars) <- foldM (closeSummaries pushGn) ([], []) (supportEdges gn)
        transition <- encodeTransition e =<< mkAdd (pushVar:equations)
        when (null equations) $ error "a push should terminate somehow, if we want to prove PAST"
        return ( transition:currs
               , if alreadyEncoded then unencodedVars ++ vars else (gnId pushGn) : (unencodedVars ++ vars)
               )
  in do
    (transitions, unencodedVars) <- foldM pushEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions)
    assert =<< mkGe var one
    return unencodedVars

encodeRewShift :: (MonadZ3 z3, Eq state, Hashable state, Show state)
  => RewVarMap
  -> (AST -> AST -> z3 AST)
  -> GraphNode state
  -> AST
  -> z3 [RewVarKey]
encodeRewShift rVarMap mkComp gn var =
  let shiftEnc (currs, newVars) e = do
        let target = to e
        (toVar, alreadyEncoded) <- lookupRewVar rVarMap target
        trans <- encodeTransition e toVar
        return ( trans:currs
            , if alreadyEncoded then newVars else target:newVars
            )
  in do
    (transitions, unencodedVars) <- foldM shiftEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions)
    assert =<< mkGe var one
    return unencodedVars
