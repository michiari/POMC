{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023-2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination (terminationQuery) where
import Prelude hiding (LT, GT)

import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint
import Pomc.Prob.OVI(ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))
import Pomc.Prob.Runtime
import Pomc.Prob.RightContexts(computeRightContexts)

import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as IOMM
import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import qualified Data.HashTable.IO as HT
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Vector.Mutable as MV
import Data.Vector((!))
import qualified Data.Vector as V

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, unless, when, forM_, forM)
import Control.Monad.ST (RealWorld)
import Pomc.Z3T (liftSTtoIO)
import Data.Maybe(fromJust, mapMaybe)
import Data.Ratio (approxRational)
import Z3.Monad hiding (Solver)
import Data.IORef (IORef, newIORef, modifyIORef', readIORef, writeIORef)
import Data.STRef (STRef, modifySTRef')
import Data.List (sort, foldl')
import qualified Debug.Trace as DBG

type TermVarMap = IORef (IOMapMap AST)
-- set of states where a semiconf terminates with positive prob.
type RightContexts = IntSet
-- global mutable data structures of this module
data TermGlobals = TermGlobals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , pastSemiconfs :: IORef IntSet
  , termVarMap :: TermVarMap
  , rewVarMap :: RewVarMap
  , eqMap :: AugEqMap (EqMapNumbersType, EqMapNumbersType)
  , eps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

newTermGlobals :: MonadZ3 z3 => Int -> STRef RealWorld Stats -> z3 TermGlobals
newTermGlobals len s = liftIO $ do
  newSS <- IOGS.new
  newBS <- IOGS.new
  newIVec <- MV.replicate len 0
  newtermMap <- IOMM.emptySized len
  newEqMap <- IOMM.emptySized len
  newLiveVars <- newIORef Set.empty
  emptyMustReachPop <- newIORef IntSet.empty
  newRewVarMap <- HT.new
  newEps <- newIORef defaultEps
  return TermGlobals  { sStack = newSS
                      , bStack = newBS
                      , iVector = newIVec
                      , pastSemiconfs = emptyMustReachPop
                      , termVarMap = newtermMap
                      , rewVarMap = newRewVarMap
                      , eqMap = (newEqMap, newLiveVars)
                      , eps = newEps
                      , stats = s
                      }

--Z3 helpers
encodeTransition :: MonadZ3 z3 => Prob -> AST -> z3 AST
encodeTransition prob_ toAST = do
  probReal <- mkRealNum prob_
  mkMul [probReal, toAST]

mkOp1 :: MonadZ3 z3 => ([AST] -> z3 AST) -> [AST] -> z3 AST
mkOp1 _ [ast] = return ast
mkOp1 mkOp asts = mkOp asts

mkAdd1 :: MonadZ3 z3 => [AST] -> z3 AST
mkAdd1 = mkOp1 mkAdd
-- end helpers

terminationQuery :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => SupportGraph state
  -> TermQuery
  -> STRef RealWorld Stats
  -> z3 (TermResult, IntSet)
terminationQuery suppGraph query oldStats = do
  globals <- newTermGlobals (V.length suppGraph) oldStats
  let gn = suppGraph ! 0
  -- setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT

  -- perform the Gabow algorithm to compute all termination probabilities
  (_, isPAST) <- dfs globals suppGraph gn (solver query)
  logInfoN $ "Is AST: " ++ show isPAST

  -- returning the computed values
  currentEps <- liftIO $ readIORef (eps globals)
  pastIds <- liftIO $ readIORef (pastSemiconfs globals)
  let actualEps = min defaultEps $ currentEps * currentEps
      intervalLogic (_, ub) Lt p = ub < p
      intervalLogic (lb, _) Gt p = lb > p
      intervalLogic (_, ub) Le p = ub <= p
      intervalLogic (lb, _) Ge p = lb >= p
      approxL (v, _) = approxRational (v - actualEps) actualEps
      approxU (_, v) = approxRational (v + actualEps) actualEps
      unlessPAST f = if isPAST then return (1,1) else f
      -- results computed with Z3
      readResults (ApproxAllQuery _) True = do
        varsVec <- liftIO $ IOMM.values (termVarMap globals)
        rUBVec <- V.mapM (fmap sum . mapM extractUpperProb) varsVec
        probMap <- liftIO $ IOMM.valuesWith (fst $ eqMap globals) (\(PopEq d) -> d)
        let lowerProbRationalMap = V.map (sum . map approxL) probMap
        return (ApproxAllResult (lowerProbRationalMap, rUBVec))
      readResults (ApproxSingleQuery _) True = do
        (lb, ub) <- unlessPAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (ApproxSingleResult (lb, ub))
      readResults (CompQuery comp bound _) True = do
        (lb, ub) <- unlessPAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return $ toTermResult $ intervalLogic (lb,ub) comp bound
      -- results computed with OVI
      readResults (ApproxAllQuery _) False = liftIO $ do
        probMap <- liftIO $ IOMM.valuesWith (fst $ eqMap globals) (\(PopEq d) -> d)
        let upperProbRationalMap = V.map (sum . map approxU) probMap
        let lowerProbRationalMap = V.map (sum . map approxL) probMap
        return (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap))
      readResults (ApproxSingleQuery _) False = do
        (lb, ub) <- unlessPAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return (ApproxSingleResult (lb, ub))
      readResults (CompQuery comp bound _) False = do
        (lb, ub) <- unlessPAST $ retrieveInitialPush actualEps (eqMap globals) gn
        return $ toTermResult $ intervalLogic (lb,ub) comp bound

  (,pastIds) <$> readResults query (useZ3 $ solver query)

-- encoding helpers --
retrieveInitialPush :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => EqMapNumbersType
  -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
  -> GraphNode state
  -> z3 (Prob, Prob)
retrieveInitialPush eps eqs gn = let
  foldUBs prob_ pushEqs = (fromRational prob_) * sum (map (\(_, PopEq (_, n)) -> n) pushEqs)
  foldLBs prob_ pushEqs = (fromRational prob_) * sum (map (\(_, PopEq (n, _)) -> n) pushEqs)
  updateLB prob_ pushEqs accLB = (accLB + foldLBs prob_ pushEqs)
  updateUB prob_ pushEqs accUB = (accUB + foldUBs prob_ pushEqs)
  toRationalLB b = approxRational (b - eps) eps
  toRationalUB b = approxRational (b + eps) eps
  Push _ pushMap = gnEdges gn
  in do
    (lb, ub) <- foldM (\(accLB, accUB) (idx, prob_) -> do
      pushEqs <- retrieveEquations eqs idx
      let newAccUB = updateUB prob_ pushEqs accUB
          newAccLB = updateLB prob_ pushEqs accLB
      return (newAccLB, newAccUB)
      ) (0, 0) (IntMap.toList pushMap)
    return (toRationalLB lb, toRationalUB ub)

-- helpers
addtoPath :: TermGlobals -> Int -> IO ()
addtoPath globals gnId_ = do
  IOGS.push (sStack globals) gnId_
  sSize <- IOGS.size $ sStack globals
  MV.unsafeWrite (iVector globals) gnId_ sSize
  IOGS.push (bStack globals) sSize

merge :: TermGlobals -> Int -> IO ()
merge globals gnId_ = do
  iVal <- MV.unsafeRead (iVector globals) gnId_
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

-- functions for Gabow algorithm
dfs :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => TermGlobals
  -> SupportGraph state
  -> GraphNode state
  -> Solver
  -> z3 (RightContexts, Bool)
dfs globals suppGraph gn solv =
  let gnId_ = gnId gn
      transitionCases (Pop popMap) = encodePopAndSolveSCC globals gnId_ popMap (useZ3 solv)
      transitionCases (Shift shiftMap) = do
        -- add current graphNode to the path
        liftIO $ addtoPath globals gnId_
        -- explore shift transitions
        (rightContexts, dPAST) <- V.unzip <$> V.mapM follow (V.fromList . IntMap.keys $ shiftMap)
        createComponent globals suppGraph gnId_ solv (IntSet.unions rightContexts, V.and dPAST)
      transitionCases (Push suppSet pushMap) = do
        -- add current graphNode to the path
        liftIO $ addtoPath globals gnId_
        -- explore push transitions 
        (pushRightContexts, pushdPAST) <- V.unzip <$> V.mapM follow (V.fromList . IntMap.keys $ pushMap)
        -- explore support transitions 
        (suppRightContexts, suppdPAST) <- V.unzip <$> V.mapM follow (V.fromList . IntSet.elems $ suppSet)
        if gnId gn == 0 
          then do 
            return (IntSet.unions pushRightContexts, V.and pushdPAST) 
          else createComponent globals suppGraph gnId_ solv 
            (IntSet.unions suppRightContexts, V.and suppdPAST && V.and pushdPAST)

      cases nextGn iVal
        | (iVal == 0) = do
            (cntxs, isPAST) <-  dfs globals suppGraph nextGn solv
            updatedIVal <- liftIO (MV.unsafeRead (iVector globals) (gnId nextGn))
            -- small performance optimization to avoid unions between overlapping sets
            if updatedIVal > 0 then return (IntSet.empty, isPAST) else return (cntxs, isPAST)
        | (iVal < 0) = liftIO $ do
            cntxs <- retrieveRightContexts (eqMap globals) (gnId nextGn)
            isPAST <- IntSet.member (gnId nextGn) <$> readIORef (pastSemiconfs globals)
            return (cntxs, isPAST)
        | (iVal > 0) = liftIO $ merge globals (gnId nextGn) >> return (IntSet.empty, True)
      follow id_ = liftIO (MV.unsafeRead (iVector globals) id_) >>= cases (suppGraph ! id_)
  in transitionCases (gnEdges gn)

createComponent :: (MonadZ3 z3, MonadLogger z3, MonadFail z3)
  => TermGlobals
  -> SupportGraph state
  -> Int
  -> Solver
  -> (RightContexts, Bool)
  -> z3 (RightContexts, Bool)
createComponent globals suppGraph gnId_ solv (rightCnxts, dPAST) = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ MV.unsafeRead (iVector globals) gnId_
  let mkComp = (if exactComputation solv then mkEq else mkGe)
      defaultEqs = IntMap.fromSet (const (PopEq (0,0))) rightCnxts
      createC = liftIO $ do
        -- update data structures from Gabow algorithm
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        forM_ poppedSemiconfs $ \id_ -> liftIO $ MV.unsafeWrite (iVector globals) id_ (-1)
        -- update statistics
        liftSTtoIO $ modifySTRef' (stats globals) $
          \s@Stats{sccCount = acc, largestSCCSemiconfsCount = acc1}
          -> s{sccCount = acc + 1, largestSCCSemiconfsCount = max acc1 (length poppedSemiconfs)}
        return poppedSemiconfs
      cases
        | iVal /= topB = addFixpEqs (eqMap globals) gnId_ defaultEqs >> return (rightCnxts, dPAST)
        | otherwise = createC >>= encode globals mkComp suppGraph gnId_ rightCnxts solv dPAST
  cases

-- encode = generate equations for termination probabilities
encode :: (MonadZ3 z3, MonadLogger z3, MonadFail z3)
  => TermGlobals
  -> (AST -> AST -> z3 AST)
  -> SupportGraph state
  -> Int
  -> IntSet
  -> Solver
  -> Bool
  -> [Int]
  -> z3 (RightContexts, Bool)
encode globals mkComp suppGraph gnId_ rightCnxts solv dPAST poppedSemiconfs =
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0)))
      semiconfs = sort poppedSemiconfs
      semiconfsVec = V.fromList semiconfs
      sccMembers = Set.fromAscList semiconfs
      remapSucc succ = Set.lookupIndex succ sccMembers
      remapSuccInfo (Push suppSet _) = mapMaybe remapSucc . IntSet.toList $ suppSet
      remapSuccInfo (Shift shiftMap) = mapMaybe remapSucc . IntMap.keys $ shiftMap
      remapSuccInfo (Pop _) = error "A Pop semiconf cannot occurr in a non-trivial SCC."
      enc (Push suppSet pushMap) = encodePush globals mkComp suppGraph suppSet pushMap (useZ3 solv)
      enc (Shift shiftMap) = encodeShift globals mkComp shiftMap (useZ3 solv)
      cases
        -- already know right contexts
        | [id_] <- poppedSemiconfs = do
          unless (id_ == gnId_) $ error "Encoding a different semiconf w.r.t. the current one."
          let succInfo = gnEdges $ suppGraph V.! id_
          if IntSet.null rightCnxts
            then return (rightCnxts, False)
          else do
            -- preadding also Z3 vars if needed
            logDebugN "Preadding all equations to the system..."
            liftIO $ addFixpEqs (eqMap globals) id_ (defaultEqs rightCnxts)
            when (useZ3 solv) $ do
              reset
              varList <- forM (IntSet.elems rightCnxts) $ \rc -> do
                (rc,) <$> mkFreshRealVar (show (id_, rc))
              liftIO $ IOMM.insertMap (termVarMap globals) id_ (IntMap.fromAscList varList)

            -- we need to solve the SCC
            enc succInfo id_ rightCnxts
            isPAST <- solveSCCQuery globals poppedSemiconfs suppGraph dPAST solv
            when isPAST $ do 
              DBG.trace ("These semiconfs are PAST: " ++ show poppedSemiconfs) $ return ()
              liftIO $ modifyIORef' (pastSemiconfs globals) $ IntSet.insert id_
            return (rightCnxts, isPAST)

        | otherwise = do
          -- need to recompute right contexts
          addFixpEqs (eqMap globals) gnId_ (defaultEqs rightCnxts)
          rcVec <- liftIO $ V.mapM (retrieveRightContexts (eqMap globals)) semiconfsVec
          let succVec = V.map (\id_ -> remapSuccInfo (gnEdges $ suppGraph V.! id_)) semiconfsVec

          logDebugN "Computing right contexts for each SCC member..."
          rcsMap <- liftIO $ computeRightContexts succVec rcVec

          logDebugN "Preadding all equations to the system..."
          when (useZ3 solv) reset
          V.iforM_ semiconfsVec $ \vecId_ id_ ->
            let rcs = rcsMap vecId_
            in do
              liftIO $ addFixpEqs (eqMap globals) id_ (defaultEqs rcs)
              -- preadding also Z3 vars if needed
              when (useZ3 solv) $ do
                varList <- forM (IntSet.elems rcs) $ \rc -> do
                  (rc,) <$> mkFreshRealVar (show (id_, rc))
                liftIO $ IOMM.insertMap (termVarMap globals) id_ (IntMap.fromAscList varList)

          logDebugN "Constructing the equation system for each SCC member..."
          V.iforM_ semiconfsVec $ \vecId_ id_ ->
            let rcs = rcsMap vecId_
                succInfo = gnEdges $ suppGraph V.! id_
            in unless (IntSet.null rcs) $ enc succInfo id_ rcs

          logDebugN "Solving the equation system..."
          isPAST <- solveSCCQuery globals semiconfs suppGraph dPAST solv
          when isPAST $ do 
            DBG.trace ("These semiconfs are PAST: " ++ show poppedSemiconfs) $ return ()
            liftIO 
            $ modifyIORef' (pastSemiconfs globals) $ IntSet.union (IntSet.fromList semiconfs)
          unless (gnId_ == semiconfsVec V.! 0)
            $ error "The entry semiconf to this SCC is not the smallest one in the ordering."
          return ((rcsMap 0), isPAST)
  in do
    logDebugN $ "SCC Members: " ++ show sccMembers
    cases

encodePush :: (MonadZ3 z3, MonadLogger z3)
  => TermGlobals
  -> (AST -> AST -> z3 AST)
  -> SupportGraph state
  -> IntSet
  -> IntMap Prob
  -> Bool
  -> Int
  -> RightContexts
  -> z3 ()
encodePush globals mkComp suppGraph suppSet pushMap useZ3 gnId_ rightCnxts = do
  augPushInfo <- forM (IntMap.toList pushMap) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (id_, prob_, encodedRCs)
  let suppSemiconfs = map (suppGraph !) . IntSet.toList $ suppSet
  augSuppInfo <- forM suppSemiconfs $ \s ->
    let suppEndsId = getId . fst . semiconf $ s
        id_ = gnId s
    in do
      encodedRCs <- retrieveRightContexts (eqMap globals) id_
      return (suppEndsId, id_, encodedRCs)
      
  let createTerm suppRC = PushEq
        [(prob_, (pushId_, pushRC), (suppId_, suppRC)) |
            (suppStateId_, suppId_, suppRCs) <- augSuppInfo
          , IntSet.member suppRC suppRCs
          , (pushId_, prob_, pushRCs) <- augPushInfo
          , pushRC <- IntSet.toList pushRCs
          , pushRC == suppStateId_
        ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts
  -- add equations
  addFixpEqs (eqMap globals) gnId_ terms
  liftSTtoIO $ modifySTRef' (stats globals) $
    \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
  logDebugN $ "Encoding Push: " ++ show gnId_ ++ " = PushEq " ++ show terms

  -- encoding equations in Z3 
  when useZ3 $ forM_ (IntMap.toList terms) $ \(rc, PushEq summands) -> do
    var <- liftIO $ fromJust <$> IOMM.lookupValue (termVarMap globals) gnId_ rc
    transitions <- forM summands $ \(prob_, pushVarKey, suppVarKey) -> do
      pushVar <- liftIO $ fromJust <$> uncurry (IOMM.lookupValue (termVarMap globals)) pushVarKey
      suppVar <- liftIO $ fromJust <$> uncurry (IOMM.lookupValue (termVarMap globals)) suppVarKey
      encodeTransition prob_ =<< mkMul [pushVar, suppVar]
    assert =<< mkComp var =<< mkAdd1 transitions

encodeShift :: (MonadZ3 z3, MonadLogger z3)
  => TermGlobals
  -> (AST -> AST -> z3 AST)
  -> IntMap Prob
  -> Bool
  -> Int
  -> IntSet
  -> z3 ()
encodeShift globals mkComp shiftMap useZ3 gnId_ rightCnxts = do
  augShiftInfo <- forM (IntMap.toList shiftMap) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (id_, prob_, encodedRCs)
  let createTerm rc = ShiftEq [ (prob_, (shiftId_, rc)) |
                                (shiftId_, prob_, shiftRCs) <- augShiftInfo,
                                IntSet.member rc shiftRCs
                              ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts
  -- add equations and compute some statistics
  addFixpEqs (eqMap globals) gnId_ terms
  liftSTtoIO $ modifySTRef' (stats globals)
    $ \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
  logDebugN $ "Encoding Shift: " ++ show gnId_ ++ " = ShiftEq " ++ show terms
  -- encode equations in Z3
  when useZ3 $ forM_ (IntMap.toList terms) $ \(rc, ShiftEq summands) -> do
    var <- liftIO $ fromJust <$> IOMM.lookupValue (termVarMap globals) gnId_ rc
    transitions <- forM summands $ \(prob_, shiftId_) -> do
      shiftVar <- liftIO $ fromJust <$> uncurry (IOMM.lookupValue (termVarMap globals)) shiftId_
      encodeTransition prob_ shiftVar
    assert =<< mkComp var =<< mkAdd1 transitions

encodePopAndSolveSCC :: (MonadZ3 z3, MonadLogger z3)
  => TermGlobals
  -> Int
  -> IntMap Prob
  -> Bool
  -> z3 (IntSet, Bool)
encodePopAndSolveSCC globals gnId_ popMap useZ3 =
  let distr = IntMap.map (\n -> PopEq (fromRational n, fromRational n)) popMap
  in do
    -- update data structures from Gabow algorithm 
    liftSTtoIO $ MV.unsafeWrite (iVector globals) gnId_ (-1)
    -- add pop transitions
    addFixpEqs (eqMap globals) gnId_ distr
    -- mark this semiconf as past
    liftIO $ modifyIORef' (pastSemiconfs globals) $ IntSet.insert gnId_

    -- encode pop transitions in Z3 
    when useZ3 $ forM_ (IntMap.toList popMap) $ \(rc, prob_) -> do
      solvedVar <- mkRealNum prob_
      liftIO $ IOMM.insert (termVarMap globals) gnId_ rc solvedVar

    -- compute some statistics
    liftSTtoIO $ modifySTRef' (stats globals) $
      \s@Stats{sccCount = acc, largestSCCSemiconfsCount = acc1, equationsCount = acc2}
      -> s{sccCount = acc + 1, largestSCCSemiconfsCount = max acc1 1, equationsCount = acc2 + length distr}
    logDebugN $ "Encoding Pop: " ++ show gnId_ ++ " = PopEq " ++ show distr
    return (IntMap.keysSet distr, True)

updateUpperBoundsOVI :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
 => TermGlobals
  -> ProbVec EqMapNumbersType
  -> z3 [((Int,Int), Double)]
updateUpperBoundsOVI globals lowerBound = do 
  let eqs = eqMap globals
  startUpper <- startTimer
  logDebugN "Using OVI to update upper bounds..."
  oviRes <- ovi defaultOVISettingsDouble eqs snd lowerBound
  rCertified <- oviToRational defaultOVISettingsDouble eqs snd oviRes
  unless rCertified $ error "Cannot deduce a rational certificate for this semiconf."
  unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bound on the termination probabilities."

  -- adding upper bounds to the system
  varKeys <- liveVariables eqs
  let bounds = V.zip3 varKeys lowerBound (oviUpperBound oviRes)
  upperBoundWithKeys <- V.mapM ( \(varKey, l, p) -> do
      addFixpEq eqs varKey (PopEq (l,p))
      return (varKey, p)
    ) bounds
  tUpper <- stopTimer startUpper True
  liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper})
  return $ V.toList upperBoundWithKeys

updateUpperBoundsZ3 :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
 => TermGlobals
  -> ProbVec EqMapNumbersType
  -> z3 [((Int,Int), Double)]
updateUpperBoundsZ3 globals lowerBound = 
  let eqs = eqMap globals
      tVarMap = termVarMap globals
      doAssert approxFracVec currentEps = do
        push -- create a backtracking point
        epsReal <- mkRealNum currentEps

        V.forM_ approxFracVec (\(varKey, pRational) -> do
            var <- liftIO $ fromJust <$> uncurry (IOMM.lookupValue tVarMap) varKey
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
                liftIO (writeIORef (eps globals) (2 * currentEps))
                pop 1 --backtrack
                doAssert approxFracVec (2 * currentEps) -- backtrack one point and restart
            | otherwise -> error "Maximum tolerance reached when solving SCC."
          _ -> error "Undefinite result when checking an SCC."
  in do 
    currentEps <- liftIO $ readIORef (eps globals)
    startUpper <- startTimer
    logDebugN "Approximating via Value Iteration + z3"
    -- we don't allow using Newton here, as it is definitively worthless.
    -- we are recomputing a lower bound using upper bounds as coefficients (that is why snd)
    approxVec <- approxFixpWithHint eqs snd defaultEps defaultMaxIters lowerBound
    let approxFracVec = toRationalProbVec defaultEps approxVec
    logDebugN "Asserting lower and upper bounds computed from value iteration, and getting a model"
    varKeys <- liveVariables eqs
    model <- doAssert (V.zip varKeys approxFracVec) (min defaultTolerance currentEps) -- currentEps is initialized with defaultEps

    -- actual updates
    upperBound <- foldM (\acc (varKey, l) -> do
      varAST <- liftIO $ fromJust <$> uncurry (IOMM.lookupValue tVarMap) varKey
      ubAST <- fromJust <$> eval model varAST
      ubDouble <- extractUpperDouble ubAST
      liftIO $ uncurry (IOMM.insert tVarMap) varKey ubAST
      addFixpEq eqs varKey (PopEq (l, ubDouble))
      return ((varKey, ubDouble):acc)
      ) [] (V.zip varKeys lowerBound)

    tUpper <- stopTimer startUpper upperBound
    liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tUpper })
    return upperBound

-- note that we consider SCCs in the semiconfiguration graph:
-- each SCC in the graph might correspond to multiple SCCs in the equation system
-- however, Newton's method is guaranteed to converge in this case as well.
solveSCCQuery :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => TermGlobals
  -> [Int]
  -> SupportGraph state
  -> Bool
  -> Solver
  -> z3 Bool
solveSCCQuery globals sccMembers suppGraph dPAST solv = do
  let eqs = eqMap globals
      tVarMap = termVarMap globals
      rVarMap = rewVarMap globals
      augTolerance = 1000 * defaultTolerance

  -- preprocessing to solve variables by backpropagating
  solvedLVars <- preprocessApproxFixp eqs fst
  solvedUvars <- preprocessApproxFixp eqs snd
  let zipSolved = zip solvedLVars solvedUvars
  forM_ zipSolved $ \((varKey, l), (_, u)) -> do
    addFixpEq eqs varKey (PopEq (l,u))
    when (useZ3 solv) $ do
      ubAST <- mkRealNum (u :: Double)
      liftIO $ uncurry (IOMM.insert tVarMap) varKey ubAST
    
  unsolvedVars <- liveVariables eqs
  liftSTtoIO $ modifySTRef' (stats globals) $ 
    \s@Stats{ largestSCCNonTrivialEqsCount = acc, nonTrivialEquationsCount = acc1} 
      -> s{largestSCCNonTrivialEqsCount = max acc (length unsolvedVars), 
          nonTrivialEquationsCount = acc1 + length unsolvedVars}

  -- solving remaining variables and compute upper bounds
  let len = V.length unsolvedVars
      zVec = V.replicate len 0
      updateLowerBound
        -- apply Newton's method only up to augTolerance, Newton's methods becomes instable when dealing with very small deltas
        | useNewton solv = approxFixpNewtonWithHint eqs fst augTolerance defaultEps defaultMaxIters defaultMaxIters zVec
        | otherwise = approxFixpWithHint eqs fst defaultEps defaultMaxIters zVec
      cases
        | null unsolvedVars = return []
        | useZ3 solv = updateLowerBound >>= updateUpperBoundsZ3 globals
        | otherwise = updateLowerBound >>= updateUpperBoundsOVI globals
      
  upperBound <- cases
  
  -- computing the PAST certificate (if needed)
  let addProb m ((scId_, _), b) = IntMap.insertWith (+) scId_ b m
      ubTermProbs = IntMap.toList $ foldl' addProb IntMap.empty (upperBound ++ solvedUvars)
      nonPASTprobs = null ubTermProbs || all (\(_,ub) -> ub < 1 - augTolerance) ubTermProbs
      pASTprobs = not (null ubTermProbs) && all (\(_,ub) -> ub > 1 - augTolerance) ubTermProbs
      exactPASTprobs = not (null ubTermProbs) && all (\(_,ub) -> ub > 1 - defaultTolerance) ubTermProbs
      pASTCertCases
        | exactComputation solv = return exactPASTprobs
        | not dPAST && pASTprobs =
          error $ "Descendants are not PAST but these semiconfs have termination upper bounds equal to 1: " ++ show ubTermProbs ++ " - scc Members: " ++ show sccMembers
        | nonPASTprobs = logDebugN "The upper bound is enough to prove non AST" >> return False
        | otherwise = do
          startPast <- startTimer
          pastRes <- certifyPAST sccMembers eqs rVarMap suppGraph mkGe pASTprobs
          tPast <- stopTimer startPast pastRes
          liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { pastTime = pastTime s + tPast})
          return True

  logDebugN $ unlines
    [ "Computed upper bounds: " ++ show upperBound
    , "SCC Members: " ++ show sccMembers
    , "Computed upper bounds on termination probabilities: " ++ show ubTermProbs
    , "Do all the descendant terminate almost surely? " ++ show dPAST
    , "Are the upper bounds proving not AST? " ++ show nonPASTprobs
    , "DefaultTolerance: " ++ show defaultTolerance
    ]

  pASTCertCases

