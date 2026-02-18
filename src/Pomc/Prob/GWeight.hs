{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.GWeight
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
module Pomc.Prob.GWeight ( Delta(..)
                         , GWeightGlobals(..)
                         , newGWeightGlobals
                         , weightQuerySCC
                         ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType, Stats(..))
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProBitencoding)
import Pomc.Prob.RightContexts(RightContexts, computeRightContexts)
import Pomc.Z3T (liftSTtoIO)

import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)
import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))
import Pomc.SatUtil

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS
import qualified Pomc.IOMapMap as IOMM
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.Vector(Vector)
import qualified Data.Vector as V
import qualified Data.Set as Set
import qualified Data.HashTable.IO as HT

import Control.Monad.ST (RealWorld)
import Data.STRef (STRef, modifySTRef')
import Control.Monad(unless, when, foldM, forM_, forM)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Maybe(catMaybes, fromJust, isJust, isNothing, mapMaybe )
import Data.Hashable(Hashable)
import GHC.IO (stToIO)
import Data.IORef (IORef, readIORef, newIORef)
import Data.Ratio (approxRational, (%))
import Control.Applicative ((<|>))
import Data.List (sort)

-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , proBitenc :: ProBitencoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> [(state, Prob)] -- deltaPush relation
  , deltaShift :: state -> [(state, Prob)] -- deltaShift relation
  , deltaPop :: state -> state -> [(state, Prob)] -- deltapop relation
  , consistentFilter :: state -> Bool
  }

-- either info for a push, or info for a shift
-- in the push info, tuples are pais (suppStateId_, suppSemiconfId_), 
-- where suppStateId_ is the id of the state in the suppSemiconf
type SuccInfo = Either (Vector (Int, Int), IntMap Prob) (IntMap Prob)

-- global variables for computing weights of support edges in graph H 
-- with respect to the prob. of the support transition in the support chain
data GWeightGlobals = GWeightGlobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , sStack     :: IOStack (Int, SuccInfo)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , eqMap :: AugEqMap (EqMapNumbersType,EqMapNumbersType)
  , stats :: STRef RealWorld Stats
  }

newGWeightGlobals :: (MonadIO m) => Int -> STRef RealWorld Stats -> m GWeightGlobals
newGWeightGlobals len stats = liftIO $ do
  newIdSeq <- newIORef 0
  newGraphMap <- HT.newSized len
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVector <- HT.newSized len
  newLowerEqMap <- IOMM.emptySized len
  newLowerLiveVars <- newIORef Set.empty
  return GWeightGlobals { idSeq = newIdSeq
                         , graphMap = newGraphMap
                         , sStack = newSStack
                         , bStack = newBStack
                         , iVector = newIVector
                         , eqMap = (newLowerEqMap, newLowerLiveVars)
                         , stats = stats
                         }

-- compute weigths of a support edge in H with respect to the support transition
weightQuerySCC :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => GWeightGlobals
  -> SIdGen RealWorld state
  -> Delta state -- delta relation of the augmented opa
  -> Vector [Stack state]
  -> Vector (Vector (StateId state))
  -> state -- current state
  -> state -- target state
  -> Bool
  -> m (Prob, Prob)
weightQuerySCC globals sIdGen delta suppStarts suppEnds current target useNewton = do
  q <- liftSTtoIO $ wrapState sIdGen current
  targetState <- liftSTtoIO $ wrapState sIdGen target
  let semiconf = (q, Nothing)
      decodedSemiconf = decode semiconf
      targetId = getId targetState
      approx eps (d,c) = (approxRational (d - eps) eps, approxRational (c + eps) eps)
  maybeSemiconfId <- liftIO $ HT.lookup (graphMap globals) decodedSemiconf
  (lb, ub) <- case maybeSemiconfId of
    Just _ -> do
      -- directly reading the result
      liftIO $ approx defaultEps <$> retrieveValue globals sIdGen delta q targetId
    Nothing -> do
      newId <- liftIO $ freshIOPosId (idSeq globals)
      liftIO $ HT.insert (graphMap globals) decodedSemiconf newId
      -- encoding the whole support
      _ <- dfs globals sIdGen delta suppStarts suppEnds semiconf newId useNewton
      liftIO $ approx defaultEps <$> retrieveValue globals sIdGen delta q targetId

  let truncatedLB = min 1 lb
      truncatedUB = min 1 ub
  logInfoN $ "Returning weights: " ++ show (truncatedLB, truncatedUB)
  when (lb > ub || lb > 1 || ub - lb > 1 % 50) $
    error $ "unsound or too loose bounds on weights for this support transition: " ++ show (lb,ub)
  return (truncatedLB, truncatedUB)

retrieveValue :: (SatState state, Eq state, Hashable state, Show state)
  => GWeightGlobals
  -> SIdGen RealWorld state
  -> Delta state
  -> StateId state
  -> Int
  -> IO (EqMapNumbersType,EqMapNumbersType)
retrieveValue globals sIdGen delta q suppId =
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      newG = Just (qProps, q)
      pushEnc acc@(accL, accU) (p, prob_) = do
        pushId <- fromJust <$> HT.lookup (graphMap globals) (decode (p, newG))
        maybeEq <- retrieveEquation (eqMap globals) (pushId, suppId)
        let PopEq (l,u) = fromJust maybeEq
            dProb_ = fromRational prob_
            newAccL = (dProb_ * l) + accL
            newAccU = (dProb_ * u) + accU
        if isJust maybeEq
          then return (newAccL, newAccU)
          else return acc
  in do
    newStates <- forM ((deltaPush delta) qState)
      $ \(unwrapped, prob_) -> (,prob_) <$> stToIO (wrapState sIdGen unwrapped)
    liftSTtoIO $ modifySTRef' (stats globals) 
      $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
    foldM pushEnc (0,0) newStates

-- utilities for Gabow algorithm
lookupIValue :: GWeightGlobals -> Int -> IO Int
lookupIValue globals scId_ = do
  maybeIval <- HT.lookup (iVector globals) scId_
  maybe (return 0) return maybeIval

lookupSemiconf :: GWeightGlobals -> (StateId state, Stack state) -> IO Int
lookupSemiconf globals semiconf = do
  maybeId <- HT.lookup (graphMap globals) (decode semiconf)
  actualId <- maybe (freshIOPosId (idSeq globals)) return maybeId
  when (isNothing maybeId) $ HT.insert (graphMap globals) (decode semiconf) actualId
  return actualId

addtoPath :: GWeightGlobals -> (Int, SuccInfo) -> IO ()
addtoPath globals (scId_, succInfo) = do
  IOGS.push (sStack globals) (scId_, succInfo)
  sSize <- IOGS.size $ sStack globals
  HT.insert (iVector globals) scId_ sSize
  IOGS.push (bStack globals) sSize

merge :: GWeightGlobals -> Int -> IO ()
merge globals scId_ = do
  iVal <- fromJust <$> HT.lookup (iVector globals) scId_
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

dfs :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => GWeightGlobals
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector [Stack state]
  -> Vector (Vector (StateId state))
  -> (StateId state, Stack state) -- current semiconf
  -> Int
  -> Bool
  -> m RightContexts
dfs globals sIdGen delta suppStarts suppEnds (q,g) scId_ useNewton =
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      transitionCases
        | (isNothing g) || precRel == Just Yield = do
            --unless ((consistentFilter delta) qState) $ error "inconsistent state in a push"
            -- computing relevant information for transitions from this semiconf
            let (pstates, probs) = unzip $ (deltaPush delta) qState
            pushStates <- liftIO $ liftSTtoIO $ wrapStates sIdGen pstates
            let pushSemiconfs = V.map (, Just (qProps, q)) pushStates
            pushSCIds <- liftIO $ V.mapM (lookupSemiconf globals) pushSemiconfs
            let isConsistentOrPop p = let s = getState p in
                  (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) s) == Just Take)
                  || (consistentFilter delta) s
                suppStates = V.filter isConsistentOrPop . fromJust $ (suppEnds V.!? (getId q)) <|> Just (V.empty)
                suppStatesIds = V.map decodeStateId suppStates
                suppSemiconfs = V.map (, g) suppStates

            suppSCIds <- if isNothing g -- do not go over the support
              then return V.empty 
              else liftIO $ V.mapM (lookupSemiconf globals) suppSemiconfs

            let suppSet = V.zip suppStatesIds suppSCIds
                pushMap = IntMap.fromListWith (+) (zip (V.toList pushSCIds) probs)
                transInfo = Left (suppSet, pushMap)
            -- add current semiconf to the path 
            liftIO $ addtoPath globals (scId_, transInfo)
            -- explore push transitions
            mapM_ follow (V.zip pushSemiconfs pushSCIds)
            --explore support transitions
            if isNothing g 
              then do 
                liftSTtoIO $ modifySTRef' (stats globals) $
                  \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
                return IntSet.empty 
              else do
              rightContexts <- IntSet.unions <$> V.mapM follow (V.zip suppSemiconfs suppSCIds)
              createComponent globals scId_ useNewton rightContexts

        | precRel == Just Equal = do
            --unless ((consistentFilter delta) qState) $ error "inconsistent state in a shift"
            -- computing relevant information for transitions from this semiconf
            let (sStates, probs) = unzip $ (deltaShift delta) qState
            shiftStates <- liftIO $ liftSTtoIO $ wrapStates sIdGen sStates
            let shiftSemiconfs = V.map (, Just (qProps, snd . fromJust $ g)) shiftStates
            nSCIds <- liftIO $ V.mapM (lookupSemiconf globals) shiftSemiconfs
            let shiftInfo = Right (IntMap.fromListWith (+) (zip (V.toList nSCIds) probs))
            
            -- add current semiconf to the path
            liftIO $ addtoPath globals (scId_, shiftInfo)
            -- explore shift transitions
            rightContexts <- IntSet.unions <$> V.mapM follow (V.zip shiftSemiconfs nSCIds)
            createComponent globals scId_ useNewton rightContexts

        | precRel == Just Take = liftIO $ encodePopAndSolveSCC (q,g) scId_ globals sIdGen delta suppStarts
        | otherwise = error "unreachable error"

      cases nextSemiconf nSCId iVal
        | (iVal == 0) = do
            cntxs <- dfs globals sIdGen delta suppStarts suppEnds nextSemiconf nSCId useNewton
            updatedIVal <- liftIO $ fromJust <$> HT.lookup (iVector globals) nSCId
            -- small performance optimization to avoid unions between overlapping sets
            if updatedIVal > 0 then return IntSet.empty else return cntxs

        | (iVal < 0)  = liftIO $ retrieveRightContexts (eqMap globals) nSCId
        | (iVal > 0)  = liftIO $ merge globals nSCId >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow (nextSemiconf, nSCId) = do
        iVal <- liftIO $ lookupIValue globals nSCId
        cases nextSemiconf nSCId iVal
  in transitionCases

createComponent :: (MonadIO m, MonadLogger m)
  => GWeightGlobals
  -> Int
  -> Bool
  -> IntSet
  -> m IntSet
createComponent globals scId_ useNewton rightCnxts = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ fromJust <$> HT.lookup (iVector globals) scId_
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0))) rightCnxts
      createC = liftIO $ do
        -- update data structures from Gabow algorithm
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is the current scId_
        forM_ (map fst poppedSemiconfs) $ \id_ -> HT.insert (iVector globals) id_ (-1)
        -- update statistics
        liftSTtoIO $ modifySTRef' (stats globals) $
          \s@Stats{largestSCCSemiconfsCountQuant = acc, sccCountQuant = acc1}
          -> s{largestSCCSemiconfsCountQuant = max acc (length poppedSemiconfs), sccCountQuant = acc1 + 1}
        return poppedSemiconfs
      cases
        | iVal /= topB = addFixpEqs (eqMap globals) scId_ defaultEqs >> return rightCnxts
        | otherwise = createC >>= encode globals useNewton scId_ rightCnxts
  cases

-- encoding helpers
-- encode = generate the equation system for variable pairs (scId_, rightContext) to determine fraction f
encode :: (MonadIO m, MonadLogger m)
  => GWeightGlobals
  -> Bool
  -> Int
  -> IntSet
  -> [(Int, SuccInfo)]
  -> m IntSet
encode globals useNewton scId_ rightCnxts poppedSemiconfs =
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0)))
      semiconfs = sort poppedSemiconfs
      semiconfsVec = V.fromList semiconfs
      sccMembers = Set.fromAscList $ map fst semiconfs
      remapSucc succ = Set.lookupIndex succ sccMembers
      remapSuccInfo (Left (v, _)) = V.toList . V.mapMaybe (remapSucc . snd) $ v
      remapSuccInfo (Right m) = mapMaybe remapSucc . IntMap.keys $ m
      enc (Left (suppInfo, pushInfo)) = encodePush globals (suppInfo, pushInfo)
      enc (Right shiftInfo) = encodeShift globals shiftInfo
      cases
        -- already know right contexts
        | [(id_, succInfo)] <- poppedSemiconfs = do
          unless (id_ == scId_) $ error "Encoding a different semiconf w.r.t. the current one."
          unless (IntSet.null rightCnxts) $ do
            logDebugN "Preadding all equations to the system..."
            -- this is needed in case of self edges
            liftIO $ addFixpEqs (eqMap globals) id_ (defaultEqs rightCnxts)
            enc succInfo id_ rightCnxts
            solveSCCQuery globals useNewton
          return rightCnxts
        | otherwise = do
          -- need to recompute right contexts
          addFixpEqs (eqMap globals) scId_ (defaultEqs rightCnxts)
          rcVec <- liftIO $ V.mapM (\(id_,_) -> retrieveRightContexts (eqMap globals) id_) semiconfsVec
          let succVec = V.map (\(_,succInfo) -> remapSuccInfo succInfo) semiconfsVec

          logDebugN "Computing right contexts for each SCC member..."
          rcsMap <- liftIO $ computeRightContexts succVec rcVec

          logDebugN "Preadding all equations to the system..."
          liftIO $ V.iforM_ semiconfsVec $ \vecId_ (id_, _) ->
            let rcs = rcsMap vecId_
            in addFixpEqs (eqMap globals) id_ (defaultEqs rcs)

          logDebugN "Constructing the equation system for each SCC member..."
          V.iforM_ semiconfsVec $ \vecId_ (id_, succInfo) ->
            let rcs = rcsMap vecId_
            in unless (IntSet.null rcs) $ enc succInfo id_ rcs

          logDebugN "Solving the equation system..."
          solveSCCQuery globals useNewton
          unless (scId_ == fst (semiconfsVec V.! 0)) 
            $ error "The entry semiconf to this SCC is not the smallest one in the ordering."
          return (rcsMap 0)
  in do
    logDebugN $ "SCC Members: " ++ show sccMembers
    cases

encodePush :: (MonadIO m, MonadLogger m)
  => GWeightGlobals
  -> (Vector (Int,Int), IntMap Prob)
  -> Int
  -> RightContexts
  -> m ()
encodePush globals (suppInfo, pushInfo) scId_ rightCnxts = do
  augPushInfo <- forM (IntMap.toList pushInfo) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (id_, prob_, encodedRCs)
  augSuppInfo <- forM suppInfo $ \(stateId_, id_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (stateId_, id_, encodedRCs)
  let createTerm suppRC = PushEq
        [(prob_, (pushId_, pushRC), (suppId_, suppRC)) |
            (suppStateId_, suppId_,  suppRCs) <- V.toList augSuppInfo
          , IntSet.member suppRC suppRCs
          , (pushId_, prob_, pushRCs) <- augPushInfo
          , pushRC <- IntSet.toList pushRCs
          , pushRC == suppStateId_
        ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts

  -- add equations
  addLiveVars (eqMap globals) scId_ terms
  liftSTtoIO $ modifySTRef' (stats globals) $
    \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + IntMap.size terms}
  logDebugN $ "Encoding Push for semiconf " ++ show scId_ ++ ": " ++ show terms

encodeShift :: (MonadIO m, MonadLogger m)
  => GWeightGlobals
  -> IntMap Prob
  -> Int
  -> RightContexts
  -> m ()
encodeShift globals shiftInfo scId_ rightCnxts = do
  augShiftInfo <- forM (IntMap.toList shiftInfo) $ \(id_, prob_) -> do
    encodedRCs <- retrieveRightContexts (eqMap globals) id_
    return (id_, prob_, encodedRCs)
  let createTerm rc = ShiftEq [ (prob_, (shiftId_, rc)) |
                                (shiftId_, prob_, shiftRCs) <- augShiftInfo,
                                IntSet.member rc shiftRCs
                              ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts
  -- add equations
  addLiveVars (eqMap globals) scId_ terms
  liftIO $ liftSTtoIO $ modifySTRef' (stats globals)
    $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + IntMap.size terms}
  logDebugN $ "Encoding Shift for semiconf " ++ show scId_ ++ ": " ++ show terms

encodePopAndSolveSCC :: (SatState state, Eq state, Hashable state, Show state)
  => (StateId state, Stack state) -- current semiconf
  -> Int
  -> GWeightGlobals
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector [Stack state]
  -> IO IntSet
encodePopAndSolveSCC (q,g) scId_ globals sIdGen delta suppStarts =
  let qState = getState q
      r = snd . fromJust $ g
      rState = getState r
      rStacks = suppStarts V.! (getId r)
      encodePop (unwrapped, e) = do
        p <- stToIO $ wrapState sIdGen unwrapped
        let pState = getState p
            pProps = getStateProps (bitenc delta) pState
            isConsistentOrThereisApop = (consistentFilter delta) pState
              || any (\g' -> isJust g' && prec delta (fst . fromJust $ g') pProps == Just Take) rStacks
        if isConsistentOrThereisApop
          then return (Just (getId p, PopEq (fromRational e, fromRational e)))
          else return Nothing
  in do
    -- update data structures from Gabow algorithm
    HT.insert (iVector globals) scId_ (-1)
    -- encode pop transitions
    distr <- catMaybes <$> mapM encodePop ((deltaPop delta) qState rState)
    addFixpEqs (eqMap globals) scId_ (IntMap.fromList distr)
    -- compute some statistics
    liftSTtoIO $ modifySTRef' (stats globals) $
          \s@Stats{sccCountQuant = acc, largestSCCSemiconfsCountQuant = acc1, equationsCountQuant = acc2}
          -> s{sccCountQuant = acc + 1, largestSCCSemiconfsCountQuant = max acc1 1, equationsCountQuant = acc2 + length distr}
    return (IntSet.fromList (map fst distr))

-- note that we consider SCCs in the semiconfiguration graph: 
-- each SCC in the graph might correspond to multiple SCCs in the equation system
-- however, Newton's method is guaranteed to converge in this case as well.
solveSCCQuery :: (MonadIO m, MonadLogger m)
 => GWeightGlobals -> Bool -> m ()
solveSCCQuery globals useNewton = do
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
    approxVec <- if useNewton
      then approxFixpNewtonWithHint eqs fst (1000 * defaultEps) defaultEps defaultMaxIters defaultMaxIters zeroVec
      else approxFixpWithHint eqs fst defaultEps defaultMaxIters zeroVec

    -- compute upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system."
    oviRes <- ovi defaultOVISettingsDouble eqs snd approxVec
    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f."

    -- certify the result and compute some statistics
    rCertified <- oviToRational defaultOVISettingsDouble eqs snd oviRes
    unless rCertified $ error "Cannot deduce a rational certificate for this SCC when computing fraction f."
    logDebugN $ "Computed upper bounds: " ++ show (oviUpperBound oviRes)
    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals) 
      (\s@Stats{quantWeightTime = acc, nonTrivialEquationsCountQuant = acc1, largestSCCNonTrivialEqsCountQuant = acc2} 
        -> s{quantWeightTime = acc + tWeights, nonTrivialEquationsCountQuant = acc1 + varSize, largestSCCNonTrivialEqsCountQuant = max acc2 varSize})

    -- update lower and upper bounds
    let bounds = V.zip3 unsolvedVars approxVec (oviUpperBound oviRes)
    V.mapM_ (\(varKey, l,u) -> do
      addPopEq eqs varKey (PopEq (l,u))) bounds