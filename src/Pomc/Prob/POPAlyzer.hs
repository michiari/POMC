{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.POPAlyzer
   Copyright   : 2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.POPAlyzer (  Globals(..)
                           , inferenceQuery
                           ) where

import Pomc.Prob.ProbUtils
import Pomc.Prob.FixPoint
import Pomc.Z3T (liftSTtoIO)

import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.Prob.SupportGraph (SupportGraph, GraphNode (..))
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import qualified Pomc.IOMapMap as IOMM

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.IntMap as IntMap
import qualified Data.Strict.IntMap as StrictIntMap
import qualified Data.Vector as V

import qualified Data.Set as Set
import Data.Vector((!))

import Control.Monad.ST (RealWorld)
import Data.STRef (STRef, modifySTRef')
import Control.Monad(unless, foldM, forM_, forM, void)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Data.Maybe (fromJust)
import Data.Hashable(Hashable)


import qualified Data.Vector.Mutable as MV
import Data.IORef (newIORef)
import Data.Ratio (approxRational)
import Data.Bifunctor(bimap)

type PopCnxts = IntSet
type GraphNodeId = Int
data SemiconfVariables = SemiconfVariables GraphNodeId PopCnxts

data Globals state = Globals
  { sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , eqMap :: AugEqMap (EqMapNumbersType, EqMapNumbersType)
  , stats :: STRef RealWorld Stats
  }

inferenceQuery :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
    => SupportGraph state
    -> EncPrecFunc
    -> Update
    -> STRef RealWorld Stats
    -> m (Distr state, Distr state)
inferenceQuery suppGraph precFun updateStrategy oldStats = do
  newSS              <- liftIO IOGS.new
  newBS              <- liftIO IOGS.new
  newIVec            <- liftIO $ MV.replicate (V.length suppGraph) 0
  newEqMap <- liftIO IOMM.empty
  newLiveVars <- liftIO $ newIORef Set.empty
  let gn = suppGraph ! 0
      globals = Globals { sStack = newSS
                        , bStack = newBS
                        , iVector = newIVec
                        , eqMap = (newEqMap, newLiveVars)
                        , stats = oldStats
                        }
  -- compute all termination probabilities via SCC decomposition with Gabow's algorithm.
  liftIO $ addtoPath globals gn
  _ <- dfs globals suppGraph precFun gn updateStrategy
  -- returning termination probabilities of the initial semiconf
  retrieveInitialPush defaultEps (eqMap globals) suppGraph gn

retrieveInitialPush :: (MonadIO m, MonadLogger m)
    => EqMapNumbersType
    -> AugEqMap (EqMapNumbersType, EqMapNumbersType)
    -> SupportGraph state
    -> GraphNode state
    -> m (Distr state, Distr state)
retrieveInitialPush eps eqs suppGraph gn = let
  parseUBs prob_  = IntMap.map (\(PopEq (_, n)) -> (fromRational prob_) * n)
  parseLBs prob_  =  IntMap.map (\(PopEq (n, _)) -> (fromRational prob_) * n)
  updateUB prob_ pushEqs accUB = IntMap.unionWith (+) accUB (parseUBs prob_ pushEqs)
  updateLB prob_ pushEqs accLB = IntMap.unionWith (+) accLB (parseLBs prob_ pushEqs)
  toRationalLB b = approxRational (b - eps) eps
  toRationalUB b = approxRational (b + eps) eps
  decompose (q, Nothing) = (getId q, getState q)
  decompose _ = error "supports of the initial semiconf should go only to semiconfs with empty stack!"
  suppStateMap = IntMap.fromList . map (decompose . semiconf . (suppGraph !)) . IntSet.toList . supportEdges $ gn
  createLBDistr m = Distr (map (bimap (suppStateMap IntMap.!) toRationalLB) . IntMap.toList $ m)
  createUBDistr m = Distr (map (bimap (suppStateMap IntMap.!) toRationalUB) . IntMap.toList $ m)

  in do
    (lb, ub) <- foldM (\(accLB, accUB) (idx, prob_) -> do
      pushEqs <- retrieveEquationsMap eqs idx
      let newAccUB = updateUB prob_ pushEqs accUB
          newAccLB = updateLB prob_ pushEqs accLB
      return (newAccLB, newAccUB)
      ) (IntMap.empty, IntMap.empty) (StrictIntMap.toList $ internalEdges gn)
    return (createLBDistr lb, createUBDistr ub)

-- functions for Gabow algorithm
dfs :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
  => Globals state
  -> SupportGraph state
  -> EncPrecFunc
  -> GraphNode state
  -> Update
  -> m PopCnxts
dfs globals suppGraph precFun gn updateStrategy =
  let cases nextSemiconf iVal
        | (iVal == 0) = liftIO (addtoPath globals nextSemiconf) >> dfs globals suppGraph precFun nextSemiconf updateStrategy
        | (iVal < 0)  = liftIO $ retrieveRightContexts (eqMap globals) (gnId nextSemiconf)
        | (iVal > 0)  = liftIO $ merge globals nextSemiconf >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow idx = liftIO (MV.unsafeRead (iVector globals) idx) >>= cases (suppGraph ! idx)
      transitionCases
        -- pop semiconf
        | not . IntMap.null $ popContexts gn = liftIO $ encodePopAndSolveSCC globals gn
        --  push/shift semiconf
        | otherwise = do
          internalPopCntxs <- IntSet.unions <$> forM (StrictIntMap.keys $ internalEdges gn) follow
          if IntSet.null $ supportEdges gn 
            then return internalPopCntxs
            else IntSet.unions <$> forM (IntSet.toList $ supportEdges gn) follow
  in do
    popContxs <- transitionCases
    createComponent globals suppGraph precFun gn popContxs updateStrategy
    return popContxs

addtoPath :: Globals state -> GraphNode state -> IO ()
addtoPath globals gn = do
  let semiconfId = gnId gn
  IOGS.push (sStack globals) semiconfId
  sSize <- IOGS.size $ sStack globals
  MV.unsafeWrite (iVector globals) (gnId gn) sSize
  IOGS.push (bStack globals) sSize

merge ::  Globals state -> GraphNode state -> IO ()
merge globals gn = do
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

createComponent :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
  => Globals state
  -> SupportGraph state
  -> EncPrecFunc
  -> GraphNode state
  -> PopCnxts
  -> Update
  -> m ()
createComponent globals suppGraph precFun gn popContxs updateStrategy = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ MV.unsafeRead (iVector globals) (gnId gn)
  let gnId_ = gnId gn
      createC = liftIO $ do
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        forM_ poppedSemiconfs $ \e -> liftIO $ MV.unsafeWrite (iVector globals) e (-1)
        liftSTtoIO $ modifySTRef' (stats globals) $
          \s@Stats{sccCount = acc1, largestSCCSemiconfsCount = acc}
          -> s{sccCount = acc1 + 1, largestSCCSemiconfsCount = max acc (length poppedSemiconfs)}
        return poppedSemiconfs
      doEncode poppedSemiconfs = do
        let toEncode = SemiconfVariables gnId_ popContxs
            sccMembers = IntSet.fromList poppedSemiconfs
            eqs = IntMap.fromSet (const (PushEq [])) popContxs
        liftIO $ do
          -- little optimization trick
          addFixpEqs (eqMap globals) gnId_ eqs
          encode toEncode globals suppGraph precFun sccMembers
        solveSCCQuery sccMembers globals (isNewton updateStrategy)
      cases
        | iVal /= topB = return ()
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = void createC -- cannot reach a pop
  cases

-- encode = generate equations for termination probabilities
encode :: (Eq state, Hashable state, Show state)
  => SemiconfVariables
  -> Globals state
  -> SupportGraph state
  -> EncPrecFunc
  -> IntSet
  -> IO ()
encode (SemiconfVariables id_ rightCnxts) globals suppGraph precFun sccMembers =
    let gn = suppGraph ! id_
        (q,g) = semiconf gn
        qLabel = getLabel q
        precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
        cases
          | precRel == Just Yield =
              encodePush globals suppGraph gn precFun rightCnxts sccMembers

          | precRel == Just Equal =
              encodeShift globals suppGraph gn precFun rightCnxts sccMembers

          | otherwise = fail "unexpected prec rel"
    in cases

encodePush :: (Eq state, Hashable state, Show state)
  => Globals state
  -> SupportGraph state
  -> GraphNode state
  -> EncPrecFunc
  -> PopCnxts
  -> IntSet
  -> IO ()
encodePush globals suppGraph gn precFun rightCnxts sccMembers =
  let suppEnds = map (suppGraph !) . IntSet.toList $ supportEdges gn
      suppEndsIds = IntSet.fromList . map (getId . fst . semiconf) $ suppEnds

  in do
    pushInfo <- forM (StrictIntMap.toList $ internalEdges gn) $ \(id_, prob_) -> do
      encodedRCs <- retrieveRightContexts (eqMap globals) id_
      let rcs = if IntSet.member id_ sccMembers
                    then suppEndsIds -- I might discover new variables
                    -- not all encoded RCs build a support for the current left context
                    else IntSet.intersection suppEndsIds encodedRCs
      return (id_, prob_, encodedRCs, rcs)

    suppInfo <- forM suppEnds $ \s ->
      let suppEndsId = getId . fst . semiconf $ s
          id_ = gnId s
      in do
        encodedRCs <- retrieveRightContexts (eqMap globals) id_
        let rcs = if IntSet.member id_ sccMembers
                    then rightCnxts -- I might discover new variables
                    else IntSet.intersection rightCnxts encodedRCs -- I might not need all encoded right contexts
        return (suppEndsId, id_, encodedRCs, rcs)

    let pushVarKeystoEncode =
          [ SemiconfVariables id_ toEncodeRCs |
              (id_, _, encodedRCs, rcs) <- pushInfo
            , IntSet.member id_ sccMembers -- to optimize filtering
            , let toEncodeRCs = IntSet.difference rcs encodedRCs
            , not $ IntSet.null toEncodeRCs
          ]
        suppVarKeystoEncode =
          [ SemiconfVariables id_ toEncodeRCs |
            (_, id_, encodedRCs, rcs) <- suppInfo
            , IntSet.member id_ sccMembers -- to optimize filtering
            , let toEncodeRCs = IntSet.difference rcs encodedRCs
            , not $ IntSet.null toEncodeRCs
          ]
        toEncode = suppVarKeystoEncode ++ pushVarKeystoEncode
        createTerm suppRC = PushEq
          [(prob_, (pushId, pushRC), (suppId, suppRC)) |
              (suppSId, suppId, _, suppRCs) <- suppInfo
            , IntSet.member suppRC suppRCs
            , (pushId, prob_, _, pushRCs) <- pushInfo
            , pushRC <- IntSet.toList pushRCs
            , pushRC == suppSId
          ]
        terms = IntMap.fromSet createTerm rightCnxts

    addFixpEqs (eqMap globals) (gnId gn) terms
    liftSTtoIO $ modifySTRef' (stats globals) $
      \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
    -- encoding new variables (these PushEq are needed as placeholders to avoid repeatedly encode them)
    forM_ toEncode $ \(SemiconfVariables id_ toBeEncoded) ->
      let eqs = IntMap.fromSet (const (PushEq [])) toBeEncoded in
        addFixpEqs (eqMap globals) id_ eqs
    forM_ toEncode $ \v -> encode v globals suppGraph precFun sccMembers

encodeShift :: (Eq state, Hashable state, Show state)
  => Globals state
  -> SupportGraph state
  -> GraphNode state
  -> EncPrecFunc
  -> PopCnxts
  -> IntSet
  -> IO ()
encodeShift globals suppGraph gn precFun rightCnxts sccMembers = do
  shiftInfo <- forM (StrictIntMap.toList $ internalEdges gn) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    let rcs = if IntSet.member id_ sccMembers
                    then rightCnxts -- I might discover new variables
                    else IntSet.intersection rightCnxts encodedRCs
    return (id_, prob_, encodedRCs, rcs)

  let shiftVarKeystoEncode =
        [SemiconfVariables shiftId_ toEncodeRCs |
            (shiftId_, _, encodedRCs, rcs) <- shiftInfo
          , IntSet.member shiftId_ sccMembers -- to optimize filtering
          , let toEncodeRCs = IntSet.difference rcs encodedRCs
          , not $ IntSet.null toEncodeRCs
        ]
      createTerm rc = ShiftEq [ (prob_, (shiftId_, rc)) |
                                (shiftId_, prob_, _, rcs) <- shiftInfo,
                                IntSet.member rc rcs
                              ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts

  addFixpEqs (eqMap globals) (gnId gn) terms
  liftSTtoIO $ modifySTRef' (stats globals)
    $ \s@Stats{equationsCount = acc} -> s{equationsCount = acc + IntMap.size terms}
  --DBG.traceM $ "Encoding shift: " ++ show semiconfId_ ++ " = ShiftEq " ++ show terms
  -- encoding new variables (these PushEq are needed as placeholders to avoid repeatedly encode them)
  forM_ shiftVarKeystoEncode $ \(SemiconfVariables id_ toBeEncoded) ->
    let eqs = IntMap.fromSet (const (PushEq [])) toBeEncoded in
      addFixpEqs (eqMap globals) id_ eqs
  forM_ shiftVarKeystoEncode $ \qv -> encode qv globals suppGraph precFun sccMembers

encodePopAndSolveSCC :: (Eq state, Hashable state, Show state)
  => Globals state
  -> GraphNode state
  -> IO IntSet
encodePopAndSolveSCC globals gn =
    let distr = IntMap.map (\n -> PopEq (fromRational n, fromRational n)) $ popContexts gn
        id_ = gnId gn
    in do
      liftSTtoIO $ modifySTRef' (stats globals) $
        \s@Stats{sccCount = acc1, largestSCCSemiconfsCount = acc}
        -> s{sccCount = acc1 + 1, largestSCCSemiconfsCount = max acc 1}
      IOGS.pop_ (bStack globals)
      IOGS.pop_ (sStack globals)
      MV.unsafeWrite (iVector globals) id_ (-1)
      addFixpEqs (eqMap globals) id_ distr
      liftSTtoIO $ modifySTRef' (stats globals) $
        \s@Stats{equationsCount = acc} -> s{equationsCount = acc + length distr}
      return (IntMap.keysSet distr)

-- note that we consider SCCs in the semiconfiguration graph: 
-- each SCC in the graph might correspond to multiple SCCs in the equation system
solveSCCQuery :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
              => IntSet -> Globals state -> Bool -> m ()
solveSCCQuery sccMembers globals useNewton = do
  let sccLen = IntSet.size sccMembers
      eqs = eqMap globals

  -- preprocess by propagating already known values
  solvedLVars <- preprocessApproxFixp eqs fst
  solvedUvars <- preprocessApproxFixp eqs snd
  let zipSolved = zip solvedLVars solvedUvars
      updatEqMap ((k1, _), (_, 0)) = deleteFixpEq eqs k1
      updatEqMap ((k1, l), (_, u)) = addFixpEq eqs k1 (PopEq (l,u))
  forM_ zipSolved updatEqMap

  prepApprox <- preprocessZeroApproxFixp eqs fst defaultEps (sccLen + 1)
  varKeys <- liveVariables eqs
  let (zeroVars, unsolvedVars) = V.partition ((== 0) . snd) (V.zip varKeys prepApprox)
  forM_ zeroVars $ \(k, _) -> deleteFixpEq eqs k

  unless (V.null unsolvedVars) $ do
    liftSTtoIO $ modifySTRef' (stats globals) $
      \s@Stats{nonTrivialEquationsCount = acc, largestSCCNonTrivialEqsCount = acc2}
      -> s{nonTrivialEquationsCount = acc + length unsolvedVars,
          largestSCCNonTrivialEqsCount = max acc2 (length unsolvedVars)}
    startWeights <- startTimer

    -- compute lower bounds
    approxVec <- if useNewton
      then approxFixpNewtonWithHint eqs fst (1000 * defaultEps) defaultEps defaultMaxIters defaultMaxIters (V.map snd unsolvedVars)
      else approxFixpWithHint eqs fst defaultEps defaultMaxIters (V.map snd unsolvedVars)

    -- compute upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system"
    oviRes <- ovi defaultOVISettingsDouble eqs snd approxVec
    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"

    -- certify the result and compute some statistics
    rCertified <- oviToRational defaultOVISettingsDouble eqs snd oviRes
    unless rCertified $ error $ "Cannot deduce a rational certificate for this SCC when computing fraction f: " ++ show sccMembers
    logDebugN $ "Computed upper bounds: " ++ show (oviUpperBound oviRes)
    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { upperBoundTime = upperBoundTime s + tWeights })

    -- updating lower and upper bounds 
    varKeys <- liveVariables eqs
    let bounds = V.zip3 varKeys approxVec (oviUpperBound oviRes)
    V.mapM_ (\(varKey, l,u) -> do
      addFixpEq eqs varKey (PopEq (l,u))) bounds