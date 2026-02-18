{-# LANGUAGE ScopedTypeVariables #-}
{- |
   Module      : Pomc.Prob.POPAlyzer
   Copyright   : 2025-2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.POPAlyzer (infer) where

import Pomc.Prob.RightContexts (RightContexts, computeRightContexts)
import Pomc.Prob.ProbUtils
import Pomc.Prob.FixPoint
import Pomc.Prob.SupportGraph (SupportGraph, GraphNode (..), buildSupportGraph, TransitionInfo (..))
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))
import Pomc.Prob.MiniProb (Program, programToPopa, Popa (..))

import Pomc.Z3T (liftSTtoIO)
import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN)
import Pomc.Check(makeOpa, InitialsComputation(..))
import Pomc.Potl (Formula(T))
import Pomc.MiniIR (Expr)

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Pomc.IOMapMap as IOMM
import qualified Data.IntMap as IntMap
import Data.IntMap(IntMap)
import Data.Vector((!))
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Set as Set

import Control.Monad.ST (RealWorld)
import Data.STRef ( STRef, modifySTRef', newSTRef, readSTRef)
import Control.Monad(unless, foldM, forM_, forM, when)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Maybe (mapMaybe, isNothing)
import Data.IORef (newIORef)
import Data.Ratio (approxRational)
import Data.Bifunctor(bimap)
import Data.List (sort)

-- global mutable data structures of this module
data InfGlobals = InfGlobals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , eqMap :: AugEqMap (EqMapNumbersType, EqMapNumbersType)
  , stats :: STRef RealWorld Stats
  }

-- infer the posterior distribution of some expression over GLOBAL program variables
infer :: (MonadIO m, MonadFail m, MonadLogger m)
  => Update -> Program -> Double -> Expr -> m ((Distr Int, Distr Int), Stats, String)
infer upStr prog eps expr =
  let (_, groupBy, popa) = programToPopa prog Set.empty
      (tsls, tprec) = popaAlphabet popa
      (bitenc, precFunc, _, _, _, _, _, _) =
        makeOpa T IsProb (tsls, tprec) (\_ _ -> True)

      initial = popaInitial popa bitenc
      pDelta = Delta
               { bitenc = bitenc
               , proBitenc = error "proBitenc used in infer function"
               , prec = precFunc
               , deltaPush = popaDeltaPush popa bitenc
               , deltaShift = popaDeltaShift popa bitenc
               , deltaPop = popaDeltaPop popa bitenc
               , phiDeltaPush = error "phiDeltaPush used in infer function"
               , phiDeltaShift = error "phiDeltaShift used in infer function"
               , phiDeltaPop = error "phiDeltaPop used in infer function"
               }
  in do
    -- build the support graph of the input pOPA
    statistics <- liftSTtoIO $ newSTRef newStats
    (suppGraph, _) <- liftSTtoIO $ buildSupportGraph pDelta initial statistics

    -- initialize global variables of the inference module
    newSS              <- liftIO IOGS.new
    newBS              <- liftIO IOGS.new
    newIVec            <- liftIO $ MV.replicate (V.length suppGraph) 0
    newEqMap <- liftIO IOMM.empty
    newLiveVars <- liftIO $ newIORef Set.empty
    let gn = suppGraph ! 0
        globals = InfGlobals { sStack = newSS
                          , bStack = newBS
                          , iVector = newIVec
                          , eqMap = (newEqMap, newLiveVars)
                          , stats = statistics
                          }
        Push suppSet pushMap = gnEdges gn
    -- compute all termination probabilities via SCC decomposition with Gabow's algorithm.
    liftIO $ addtoPath globals 0
    _ <- dfs globals eps suppGraph gn upStr

    -- returning termination probabilities of the initial semiconf
    (lb, ub) <- retrieveValue eps (eqMap globals) suppGraph suppSet pushMap
    computedStats <- liftSTtoIO $ readSTRef statistics
    --let probMass (Distr l) = fromRational (sum $ map snd l) :: Double
    --DBG.trace ("Probability of returning(lower bound): " ++ show (probMass lb)) $ return ()
    --DBG.trace ("Probability of returning(upper bound): " ++ show (probMass ub)) $ return ()
    return ((groupBy expr lb, groupBy expr ub), computedStats, show suppGraph)

retrieveValue :: (MonadIO m, MonadLogger m, MonadFail m)
    => EqMapNumbersType
    -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
    -> SupportGraph state
    -> IntSet
    -> IntMap Prob
    -> m (Distr state, Distr state)
retrieveValue eps eqs suppGraph suppSet pushMap = 
  let
    parseUBs prob_  = IntMap.map (\(PopEq (_, n)) -> (fromRational prob_) * n)
    parseLBs prob_  =  IntMap.map (\(PopEq (n, _)) -> (fromRational prob_) * n)
    updateUB prob_ pushEqs accUB = IntMap.unionWith (+) accUB (parseUBs prob_ pushEqs)
    updateLB prob_ pushEqs accLB = IntMap.unionWith (+) accLB (parseLBs prob_ pushEqs)
    toRationalLB b = approxRational (b - eps) eps
    toRationalUB b = approxRational (b + eps) eps
    decompose (q, Nothing) = (getId q, getState q)
    decompose _ = error "supports of the initial semiconf should go only to semiconfs with empty stack!"
    suppStateMap = IntMap.fromList . map (decompose . semiconf . (suppGraph !)) . IntSet.toList $ suppSet
    createLBDistr m = Distr (map (bimap (suppStateMap IntMap.!) toRationalLB) . IntMap.toList $ m)
    createUBDistr m = Distr (map (bimap (suppStateMap IntMap.!) toRationalUB) . IntMap.toList $ m)
  in do
    (lb, ub) <- foldM (\(accLB, accUB) (idx, prob_) -> do
      pushEqs <- retrieveEquationsMap eqs idx
      let newAccUB = updateUB prob_ pushEqs accUB
          newAccLB = updateLB prob_ pushEqs accLB
      return (newAccLB, newAccUB)
      ) (IntMap.empty, IntMap.empty) (IntMap.toList pushMap)
    return (createLBDistr lb, createUBDistr ub)

addtoPath :: InfGlobals -> Int -> IO ()
addtoPath globals gnId_ = do
  IOGS.push (sStack globals) gnId_
  sSize <- IOGS.size $ sStack globals
  MV.unsafeWrite (iVector globals) gnId_ sSize
  IOGS.push (bStack globals) sSize

merge ::  InfGlobals -> Int -> IO ()
merge globals gnId_  = do
  iVal <- MV.unsafeRead (iVector globals) gnId_
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

-- functions for Gabow algorithm
dfs :: (MonadIO m, MonadLogger m, MonadFail m)
  => InfGlobals
  -> Double
  -> SupportGraph state
  -> GraphNode state
  -> Update
  -> m RightContexts
dfs globals eps suppGraph gn upStr =
  let gnId_ = gnId gn
      (_,g) = semiconf gn
      transitionCases (Pop popMap) = encodePopAndSolveSCC globals gnId_ popMap
      transitionCases (Shift shiftMap) = do
        -- add current graphNode to the path
        liftIO $ addtoPath globals gnId_
        -- explore shift transitions
        rightCnxts <- IntSet.unions <$> V.mapM follow (V.fromList . IntMap.keys $ shiftMap)
        createComponent globals eps suppGraph gnId_ rightCnxts upStr
      transitionCases (Push suppSet pushMap) = do 
        -- add current graphNode to the path
        liftIO $ addtoPath globals gnId_
        -- explore push transitions 
        V.mapM_ follow (V.fromList . IntMap.keys $ pushMap)
        -- explore support transitions 
        if isNothing g then return IntSet.empty else do
          rightContexts <- IntSet.unions <$> V.mapM follow (V.fromList . IntSet.elems $ suppSet)
          createComponent globals eps suppGraph gnId_ rightContexts upStr

      cases nextGn iVal
        | (iVal == 0) = do 
            cntxs <-  dfs globals eps suppGraph nextGn upStr
            updatedIVal <- liftIO (MV.unsafeRead (iVector globals) (gnId nextGn))
            -- small performance optimization to avoid unions between overlapping sets
            if updatedIVal > 0 then return IntSet.empty else return cntxs

        | (iVal < 0)  = liftIO $ retrieveRightContexts (eqMap globals) (gnId nextGn)
        | (iVal > 0)  = liftIO $ merge globals (gnId nextGn) >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow id_ = liftIO (MV.unsafeRead (iVector globals) id_) >>= cases (suppGraph ! id_)
  in transitionCases (gnEdges gn)

createComponent :: (MonadIO m, MonadLogger m, MonadFail m)
  => InfGlobals
  -> Double
  -> SupportGraph state
  -> Int
  -> RightContexts
  -> Update
  -> m RightContexts
createComponent globals eps suppGraph gnId_ rightCnxts upStr = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ MV.unsafeRead (iVector globals) gnId_
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0))) rightCnxts
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
        | iVal /= topB = addFixpEqs (eqMap globals) gnId_ defaultEqs >> return rightCnxts
        | otherwise = createC >>= encode globals eps suppGraph (isNewton upStr) gnId_ rightCnxts
  cases

-- encode = generate equations for termination probabilities
encode :: (MonadIO m, MonadLogger m, MonadFail m)
  => InfGlobals
  -> Double
  -> SupportGraph state
  -> Bool
  -> Int
  -> IntSet
  -> [Int]
  -> m RightContexts
encode globals eps suppGraph newton gnId_ rightCnxts poppedSemiconfs =
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0)))
      semiconfs = sort poppedSemiconfs
      semiconfsVec = V.fromList semiconfs
      sccMembers = Set.fromAscList semiconfs
      remapSucc succ = Set.lookupIndex succ sccMembers
      remapSuccInfo (Push suppSet _) = mapMaybe remapSucc . IntSet.toList $ suppSet
      remapSuccInfo (Shift shiftMap) = mapMaybe remapSucc . IntMap.keys $ shiftMap
      remapSuccInfo (Pop _) = error "A Pop semiconf cannot occurr in a non-trivial SCC."
      enc (Push suppSet pushMap) = encodePush globals suppGraph suppSet pushMap
      enc (Shift shiftMap) = encodeShift globals shiftMap
      cases
        -- already know right contexts
        | [id_] <- poppedSemiconfs = do
          unless (id_ == gnId_) $ error "Encoding a different semiconf w.r.t. the current one."
          let succInfo = gnEdges $ suppGraph V.! id_
          unless (IntSet.null rightCnxts) $ do
            logDebugN "Preadding all equations to the system..."
            -- this is needed in case of self edges
            liftIO $ addFixpEqs (eqMap globals) id_ (defaultEqs rightCnxts)
            enc succInfo id_ rightCnxts
            solveSCCQuery globals eps newton
          return rightCnxts
        | otherwise = do
          -- need to recompute right contexts
          addFixpEqs (eqMap globals) gnId_ (defaultEqs rightCnxts)
          rcVec <- liftIO $ V.mapM (retrieveRightContexts (eqMap globals)) semiconfsVec
          let succVec = V.map (\id_ -> remapSuccInfo (gnEdges $ suppGraph V.! id_)) semiconfsVec

          logDebugN "Computing right contexts for each SCC member..."
          rcsMap <- liftIO $ computeRightContexts succVec rcVec

          logDebugN "Preadding all equations to the system..."
          liftIO $ V.iforM_ semiconfsVec $ \vecId_ id_ ->
            let rcs = rcsMap vecId_
            in addFixpEqs (eqMap globals) id_ (defaultEqs rcs)

          logDebugN "Constructing the equation system for each SCC member..."
          V.iforM_ semiconfsVec $ \vecId_ id_ ->
            let rcs = rcsMap vecId_
                succInfo = gnEdges $ suppGraph V.! id_
            in unless (IntSet.null rcs) $ enc succInfo id_ rcs

          logDebugN "Solving the equation system..."
          solveSCCQuery globals eps newton
          unless (gnId_ == semiconfsVec V.! 0)
            $ error "The entry semiconf to this SCC is not the smallest one in the ordering."
          return (rcsMap 0)
  in do
    logDebugN $ "SCC Members: " ++ show sccMembers
    cases

encodePush :: (MonadIO m, MonadLogger m, MonadFail m)
  => InfGlobals
  -> SupportGraph state
  -> IntSet
  -> IntMap Prob
  -> Int
  -> RightContexts
  -> m ()
encodePush globals suppGraph suppSet pushMap gnId_ rightCnxts = do
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
  addLiveVars (eqMap globals) gnId_ terms
  liftSTtoIO $ modifySTRef' (stats globals) $
    \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
  logDebugN $ "Encoding Push: " ++ show gnId_ ++ " = PushEq " ++ show terms

encodeShift :: (MonadIO m, MonadLogger m, MonadFail m)
  => InfGlobals
  -> IntMap Prob
  -> Int
  -> RightContexts
  -> m ()
encodeShift globals shiftMap gnId_ rightCnxts = do
  augShiftInfo <- forM (IntMap.toList shiftMap) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (id_, prob_, encodedRCs)
  let createTerm rc = ShiftEq [ (prob_, (shiftId_, rc)) |
                                (shiftId_, prob_, shiftRCs) <- augShiftInfo,
                                IntSet.member rc shiftRCs
                              ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts
  -- add equations
  addLiveVars (eqMap globals) gnId_ terms
  liftSTtoIO $ modifySTRef' (stats globals)
    $ \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
  logDebugN $ "Encoding Shift: " ++ show gnId_ ++ " = ShiftEq " ++ show terms

encodePopAndSolveSCC :: (MonadIO m, MonadLogger m)
  => InfGlobals
  -> Int
  -> IntMap Prob
  -> m IntSet
encodePopAndSolveSCC globals gnId_ popMap =
  let distr = IntMap.map (\n -> PopEq (fromRational n, fromRational n)) popMap
  in do
    -- update data structures from Gabow algorithm 
    liftSTtoIO $ MV.unsafeWrite (iVector globals) gnId_ (-1)
    -- encode pop transitions
    addFixpEqs (eqMap globals) gnId_ distr

    -- compute some statistics
    liftSTtoIO $ modifySTRef' (stats globals) $
      \s@Stats{sccCount = acc, largestSCCSemiconfsCount = acc1, equationsCount = acc2}
      -> s{sccCount = acc + 1, largestSCCSemiconfsCount = max acc1 1, equationsCount = acc2 + length distr}
    return (IntMap.keysSet distr)

-- note that we consider SCCs in the semiconfiguration graph:
-- each SCC in the graph might correspond to multiple SCCs in the equation system
-- however, Newton's method is guaranteed to converge in this case as well.
solveSCCQuery :: (MonadIO m, MonadLogger m)
              => InfGlobals -> Double -> Bool -> m ()
solveSCCQuery globals eps newton = do
  let eqs = eqMap globals
  -- preprocess by propagating already known values
  solvedLVars <- preprocessApproxFixp eqs fst
  solvedUvars <- preprocessApproxFixp eqs snd
  let zipSolved = zip solvedLVars solvedUvars
      updatEqMap ((k1, l), (_, u)) = addPopEq eqs k1 (PopEq (l,u))
  forM_ zipSolved updatEqMap

  unsolvedVars <- liveVariables eqs
  unless (V.null unsolvedVars) $ do
    let varSize = V.length unsolvedVars
        zeroVec = V.replicate varSize 0
    startWeights <- startTimer

    -- compute lower bounds
    approxVec <- if newton
      then approxFixpNewtonWithHint eqs fst (1000 * eps) eps defaultMaxIters defaultMaxIters zeroVec
      else approxFixpWithHint eqs fst eps defaultMaxIters zeroVec

    -- compute upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system."
    oviRes <- ovi (defaultOVISettingsDouble eps) eqs snd approxVec
    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the termination probabilities."

    -- certify the result and compute some statistics
    rCertified <- oviToRational (defaultOVISettingsDouble eps) eqs snd oviRes
    unless rCertified $ error "Cannot deduce a rational certificate for this SCC when computing upper bounds to the termination probabilities."
    logDebugN $ "Computed upper bounds: " ++ show (oviUpperBound oviRes)
    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals)
      (\s@Stats{upperBoundTime = acc, nonTrivialEquationsCount = acc1, largestSCCNonTrivialEqsCount = acc2}
        -> s{upperBoundTime = acc + tWeights, nonTrivialEquationsCount = acc1 + varSize, largestSCCNonTrivialEqsCount = max acc2 varSize})

    -- update lower and upper bounds
    let bounds = V.zip3 unsolvedVars approxVec (oviUpperBound oviRes)
    V.mapM_ (\(varKey, l,u) -> do
      when (u - l > 0.02) $ error $ "The upper bound is too lose: " ++ show varKey ++ " = (" ++ show l ++ "," ++ show u ++ ")"
      addPopEq eqs varKey (PopEq (l,u))) bounds
