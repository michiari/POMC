{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.GReach
   Copyright   : 2023-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( GRobals(..)
                        , Delta(..)
                        , WeightedGRobals(..)
                        , newGRobals
                        , nrSemiconfs
                        , reachableStates
                        , showGrobals
                        , newWeightedGRobals
                        , weightQuerySCC
                        , freezeSuppEnds
                        , freezeSuppStarts
                        ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType, Stats(..), defaultTolerance)
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
import Pomc.Prob.RightContexts(computeRightContexts)
import qualified Pomc.Prob.ProbEncoding as PE
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

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM

import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM
import qualified Pomc.IOMapMap as IOMM

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import Data.Vector(Vector)
import qualified Data.Vector as V

import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad.ST (ST, RealWorld)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef, modifySTRef')
import Control.Monad(unless, when, foldM, forM_, forM)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Data.Maybe
import Data.Hashable(Hashable)
import Data.Bifunctor(first)

import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as BC
import qualified Data.HashTable.IO as HT

import qualified Data.Vector.Mutable as MV
import GHC.IO (stToIO)
import Data.IORef (IORef, modifyIORef', readIORef, modifyIORef', newIORef)
import Data.Ratio (approxRational, (%))
import Control.Applicative ((<|>))
import Data.List (sort)

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- global variables for detecting reachable right contexts of suppEnds edges in graph G
data GRobals s state = GRobals
  { sIdGen :: SIdGen s state
  , visited :: HashTable s (Int,Int,Int) ProbEncodedSet -- we store the recorded sat set as well
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (MapMap s (StateId state) ProbEncodedSet) -- we store the formulae satisfied in the support
  , currentInitial :: STRef s Int -- stateId of the current initial state
  }

showGrobals :: (Show state) => GRobals s state -> ST s String
showGrobals grobals = do
  s1 <- SM.showSetMap =<< readSTRef (suppStarts grobals)
  s2 <- MM.showMapMap =<< readSTRef (suppEnds grobals)
  s3 <- concatMap show <$> BC.toList (visited grobals)
  return $ "SuppStarts: " ++ s1 ++ "---- SuppEnds: " ++ s2 ++ "---- Visited: " ++ s3

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

newGRobals :: ST.ST s (GRobals s state)
newGRobals = do
  newSig <- initSIdGen
  emptyVisited <- BH.new
  emptySuppStarts <- SM.empty
  emptySuppEnds <- MM.empty
  noInitial <- newSTRef (-1 :: Int)
  return $ GRobals { sIdGen = newSig
                   , visited = emptyVisited
                   , suppStarts = emptySuppStarts
                   , suppEnds = emptySuppEnds
                   , currentInitial = noInitial
                   }

nrSemiconfs :: GRobals s state -> ST.ST s Int
nrSemiconfs grobals = BH.size (visited grobals)

reachableStates :: (SatState state, Eq state, Hashable state, Show state)
  => GRobals s state
  -> Delta state -- delta relation of the opa
  -> state -- current state
  -> ST s [(state, ProbEncodedSet)]
reachableStates globals delta state = do
  q <- wrapState (sIdGen globals) state
  currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
  if not (null currentSuppEnds)
    then return $ filter ((consistentFilter delta) . fst) . map (first getState) $ currentSuppEnds
    else do
      writeSTRef (currentInitial globals) (getId q)
      let newStateSatSet = PE.encodeSatState (proBitenc delta) state
      BH.insert (visited globals) (decode (q,Nothing)) newStateSatSet
      reach globals delta (q,Nothing) newStateSatSet
      updatedSuppEnds <- MM.lookup (suppEnds globals) (getId q)
      return $ filter ((consistentFilter delta) . fst) .  map (first getState) $ updatedSuppEnds

reach :: (SatState state, Eq state, Hashable state, Show state)
  => GRobals s state -- global variables of the algorithm
  -> Delta state -- delta relation of the opa
  -> (StateId state, Stack state) -- current semiconfiguration
  -> ProbEncodedSet -- current satset
  -> ST s ()
reach globals delta (q,g) pathSatSet = do
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases i
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && (getId q /= i) = return ()
            --unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push with empty stack in GReach " ++  show qState

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield ) =
            --unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push in GReach " ++  show qState ++ "; " ++ show g ++ ";\n\n\nPREC " ++ show precRel
            reachPush globals delta q g qState pathSatSet

        | precRel == Just Equal =
            --unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a shift in GReach " ++  show qState
            reachShift globals delta q g qState pathSatSet

        | precRel == Just Take =
            reachPop globals delta q g qState pathSatSet

        | otherwise = return ()

  iniId <- readSTRef (currentInitial globals)
  cases iniId

reachPush :: (SatState state, Eq state, Hashable state, Show state)
  => GRobals s state
  -> Delta state
  -> StateId state
  -> Stack state
  -> state
  -> ProbEncodedSet
  -> ST s ()
reachPush globals delta q g qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doPush p = reachTransition globals delta Nothing Nothing (p, Just (qProps, q))
      isConsistentOrPop p = let s = getState p in
          (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) s) == Just Take)
          || (consistentFilter delta) s
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ map fst $ (deltaPush delta) qState
    mapM_ doPush newStates
    currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
    mapM_ (\(s, supportSatSet) -> reachTransition globals delta (Just pathSatSet) (Just supportSatSet) (s,g))
      $ filter (isConsistentOrPop . fst) currentSuppEnds

reachShift :: (SatState state, Eq state, Hashable state, Show state)
      => GRobals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> state
      -> ProbEncodedSet
      -> ST s ()
reachShift globals delta _ g qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doShift p = reachTransition globals delta (Just pathSatSet) Nothing (p, Just (qProps, snd . fromJust $ g))
  in wrapStates (sIdGen globals) (map fst $ (deltaShift delta) qState) >>= mapM_ doShift

reachPop :: (SatState state, Eq state, Hashable state, Show state)
    => GRobals s state
    -> Delta state
    -> StateId state
    -> Stack state
    -> state
    -> ProbEncodedSet
    -> ST s ()
reachPop globals delta _ g qState pathSatSet =
  let gState = getState . snd . fromJust $ g
      doPop p =
        let r = snd . fromJust $ g
            pState = getState p
            pProps = getStateProps (bitenc delta) pState
            isConsistentOrPop g' = (isJust g' && prec delta (fst . fromJust $ g') pProps == Just Take)
              || (consistentFilter delta) pState
            closeSupports g' = when (isConsistentOrPop g') $ do
              lcSatSet <- fromJust <$> BH.lookup (visited globals) (decode (r,g'))
              reachTransition globals delta (Just lcSatSet) (Just pathSatSet) (p, g')
        in do
          MM.insertWith (suppEnds globals) (getId r) PE.union p pathSatSet
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ closeSupports currentSuppStarts
  in wrapStates (sIdGen globals) (map fst ((deltaPop delta) qState gState)) >>= mapM_ doPop

-- handling the transition to a new semiconfiguration
reachTransition :: (SatState state, Eq state, Hashable state, Show state)
                 => GRobals s state
                 -> Delta state
                 -> Maybe ProbEncodedSet -- the SatSet established on the path so far
                 -> Maybe ProbEncodedSet -- the SatSet of the edge (Nothing if it is not a Support edge)
                 -> (StateId state, Stack state) -- to semiconf
                 -> ST s ()
reachTransition globals delta pathSatSet mSuppSatSet dest =
  let -- computing the new set of sat formulae for the current path in the chain
    newStateSatSet = PE.encodeSatState (proBitenc delta) (getState . fst $ dest)
    newPathSatSet = PE.unions (newStateSatSet : catMaybes [pathSatSet, mSuppSatSet])
    decodedDest = decode dest
  in do
  maybeSatSet <- BH.lookup (visited globals) decodedDest
  if isNothing maybeSatSet
    then do
      -- dest semiconf has not been visited so far
      BH.insert (visited globals) decodedDest newPathSatSet
      reach globals delta dest newPathSatSet
    else do
      let recordedSatSet = fromJust maybeSatSet
      let augmentedPathSatSet = PE.unions (recordedSatSet : catMaybes [pathSatSet, mSuppSatSet])
      unless (recordedSatSet `PE.subsumes` augmentedPathSatSet) $ do
        -- dest semiconf has been visited, but with a set of sat formulae that does not subsume the current ones
        BH.insert (visited globals) decodedDest augmentedPathSatSet
        reach globals delta dest augmentedPathSatSet

freezeSuppEnds :: GRobals RealWorld state -> IO (Vector (Vector (StateId state)))
freezeSuppEnds globals = stToIO $ do
  computedSuppEnds <- readSTRef (suppEnds globals)
  V.map (V.fromList . Map.keys) <$> V.freeze computedSuppEnds

freezeSuppStarts :: GRobals RealWorld state -> IO (Vector [Stack state])
freezeSuppStarts globals = stToIO $ do
  computedSuppStarts <- readSTRef (suppStarts globals)
  V.map Set.toList <$> V.freeze computedSuppStarts

type RightContexts = IntSet
-- either info for a push, or info for a shift
-- in the push info, tuples are pais (suppStateId_, suppSemiconfId_), 
-- where suppStateId_ is the id of the state in the suppSemiconf
type SuccInfo = Either (Vector (Int, Int), IntMap Prob) (IntMap Prob)

-- global variables for computing weights of support edges in graph H 
-- with respect to the prob. of the support transition in the support chain
data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , sStack     :: IOStack (Int, SuccInfo)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , eqMap :: AugEqMap (EqMapNumbersType,EqMapNumbersType)
  , actualEps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

newWeightedGRobals :: (MonadIO m) => Int -> STRef RealWorld Stats -> m (WeightedGRobals state)
newWeightedGRobals len stats = liftIO $ do
  newIdSeq <- newIORef 0
  newGraphMap <- HT.newSized len
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVector <- HT.newSized len
  newLowerEqMap <- IOMM.emptySized len
  newLowerLiveVars <- newIORef Set.empty
  newEps <- newIORef defaultTolerance
  return WeightedGRobals { idSeq = newIdSeq
                         , graphMap = newGraphMap
                         , sStack = newSStack
                         , bStack = newBStack
                         , iVector = newIVector
                         , eqMap = (newLowerEqMap, newLowerLiveVars)
                         , actualEps = newEps
                         , stats = stats
                         }

-- compute weigths of a support edge in H with respect to the support transition
weightQuerySCC :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
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
      eps <- liftIO $ readIORef (actualEps globals)
      liftIO $ approx eps <$> retrieveValue globals sIdGen delta q targetId
    Nothing -> do
      newId <- liftIO $ freshIOPosId (idSeq globals)
      liftIO $ HT.insert (graphMap globals) decodedSemiconf newId
      -- encoding the whole support
      _ <- dfs globals sIdGen delta suppStarts suppEnds semiconf newId useNewton
      eps <- liftIO $ readIORef (actualEps globals)
      liftIO $ approx eps <$> retrieveValue globals sIdGen delta q targetId

  let truncatedLB = min 1 lb
      truncatedUB = min 1 ub
  logInfoN $ "Returning weights: " ++ show (truncatedLB, truncatedUB)
  when (lb > ub || lb > 1 || ub - lb > 1 % 50) $
    error $ "unsound or too loose bounds on weights for this support transition: " ++ show (lb,ub)
  return (truncatedLB, truncatedUB)

retrieveValue :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
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
      newStates <- mapM (\(unwrapped, prob_) -> (,prob_) <$> stToIO (wrapState sIdGen unwrapped)) $ (deltaPush delta) qState
      liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
      foldM pushEnc (0,0) newStates

-- utilities for Gabow algorithm
lookupIValue :: WeightedGRobals state -> Int -> IO Int
lookupIValue globals scId_ = do
  maybeIval <- HT.lookup (iVector globals) scId_
  maybe (return 0) return maybeIval

lookupSemiconf :: WeightedGRobals state -> (StateId state, Stack state) -> IO Int
lookupSemiconf globals semiconf = do
  maybeId <- HT.lookup (graphMap globals) (decode semiconf)
  actualId <- maybe (freshIOPosId (idSeq globals)) return maybeId
  when (isNothing maybeId) $ HT.insert (graphMap globals) (decode semiconf) actualId
  return actualId

freshIOPosId :: IORef Int -> IO Int
freshIOPosId idSeq = do
  curr <- readIORef idSeq
  modifyIORef' idSeq (+1)
  return curr

addtoPath :: WeightedGRobals state-> (Int, SuccInfo) -> IO ()
addtoPath globals (scId_, succInfo) = do
  IOGS.push (sStack globals) (scId_, succInfo)
  sSize <- IOGS.size $ sStack globals
  HT.insert (iVector globals) scId_ sSize
  IOGS.push (bStack globals) sSize

merge ::  WeightedGRobals state -> Int -> IO ()
merge globals scId_ = do
  iVal <- lookupIValue globals scId_
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

-- encoding helpers
-- encode = generate the equation system for variable pairs (scId_, rightContext) to determine fraction f
encode :: (MonadIO m, MonadLogger m)
  => WeightedGRobals state
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
          return (rcsMap 0)
  in do
    logDebugN $ "SCC Members: " ++ show sccMembers
    cases

encodePush :: (MonadIO m, MonadLogger m) => WeightedGRobals state
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
          ,  (pushId_, prob_, pushRCs) <- augPushInfo
          , pushRC <- IntSet.toList pushRCs
          , pushRC == suppStateId_
        ]
      terms :: IntMap.IntMap (FixpEq (EqMapNumbersType, EqMapNumbersType))
      terms = IntMap.fromSet createTerm rightCnxts

  -- add equations
  addFixpEqs (eqMap globals) scId_ terms
  liftSTtoIO $ modifySTRef' (stats globals) $
    \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + IntMap.size terms}
  logDebugN $ "Encoding push: " ++ show scId_ ++ " = ShiftEq " ++ show terms

encodeShift :: (MonadIO m, MonadLogger m) => WeightedGRobals state
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
  addFixpEqs (eqMap globals) scId_ terms
  liftIO $ liftSTtoIO $ modifySTRef' (stats globals)
    $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + IntMap.size terms}
  logDebugN $ "Encoding shift: " ++ show scId_ ++ " = ShiftEq " ++ show terms

encodePopAndSolveSCC :: (SatState state, Eq state, Hashable state, Show state)
  => (StateId state, Stack state) -- current semiconf
  -> Int
  -> WeightedGRobals state
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
        \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + length distr}
      return (IntSet.fromList (map fst distr))

dfs :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
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
            suppSCIds <- liftIO $ V.mapM (lookupSemiconf globals) suppSemiconfs
            let pushInfo = Left (V.zip suppStatesIds suppSCIds, IntMap.fromListWith (+) (zip (V.toList pushSCIds) probs))
            liftIO $ addtoPath globals (scId_, pushInfo)

            -- explore push transitions
            mapM_ follow (V.zip pushSemiconfs pushSCIds)
            --explore support transitions
            if isNothing g then return IntSet.empty else do
              rightContexts <- IntSet.unions <$> V.mapM follow (V.zip suppSemiconfs suppSCIds)
              createComponent globals scId_ useNewton rightContexts

        | precRel == Just Equal = do
            --unless ((consistentFilter delta) qState) $ error "inconsistent state in a shift"
            let (sStates, probs) = unzip $ (deltaShift delta) qState
            shiftStates <- liftIO $ liftSTtoIO $ wrapStates sIdGen sStates
            let shiftSemiconfs = V.map (, Just (qProps, snd . fromJust $ g)) shiftStates
            nSCIds <- liftIO $ V.mapM (lookupSemiconf globals) shiftSemiconfs
            let shiftInfo = Right (IntMap.fromListWith (+) (zip (V.toList nSCIds) probs))
            liftIO $ addtoPath globals (scId_, shiftInfo)

            -- explore shift transitions
            rightContexts <- IntSet.unions <$> V.mapM follow (V.zip shiftSemiconfs nSCIds)
            createComponent globals scId_ useNewton rightContexts

        | precRel == Just Take = liftIO $ encodePopAndSolveSCC (q,g) scId_ globals sIdGen delta suppStarts
        | otherwise = error "unreachable error"

      cases nextSemiconf nSCId iVal
        | (iVal == 0) = do
            --liftIO $ addtoPath globals nSCId
            cntxs <- dfs globals sIdGen delta suppStarts suppEnds nextSemiconf nSCId useNewton
            updatedIVal <- liftIO $ lookupIValue globals nSCId
            -- small performance optimization to avoid unions between overlapping sets
            if updatedIVal > 0 then return IntSet.empty else return cntxs

        | (iVal < 0)  = liftIO $ retrieveRightContexts (eqMap globals) nSCId
        | (iVal > 0)  = liftIO $ merge globals nSCId >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow (nextSemiconf, nSCId) = do
        iVal <- liftIO $ lookupIValue globals nSCId
        cases nextSemiconf nSCId iVal
  in transitionCases

createComponent :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> Int
  -> Bool
  -> IntSet
  -> m IntSet
createComponent globals scId_ useNewton rightContexts = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ lookupIValue globals scId_
  let defaultEqs = IntMap.fromSet (const (PopEq (0,0))) rightContexts
      createC = liftIO $ do
        -- update data structures from Gabow algorithm
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is the current scId_
        forM_ (map fst poppedSemiconfs) $ \id_ -> HT.insert (iVector globals) id_ (-1)
        -- update statistics
        liftSTtoIO $ modifySTRef' (stats globals) $
          \s@Stats{sccCountQuant = acc1, largestSCCSemiconfsCountQuant = acc}
          -> s{sccCountQuant = acc1 + 1, largestSCCSemiconfsCountQuant = max acc (length poppedSemiconfs)}
        return poppedSemiconfs
      cases
        | iVal /= topB = addFixpEqs (eqMap globals) scId_ defaultEqs >> return rightContexts
        | otherwise = createC >>= encode globals useNewton scId_ rightContexts -- can reach a pop
  cases

-- note that we consider SCCs in the semiconfiguration graph: 
-- each SCC in the graph might correspond to multiple SCCs in the equation system
-- however, Newton's method is guaranteed to converge in this case as well.
solveSCCQuery :: (MonadIO m, MonadLogger m)
              => WeightedGRobals state -> Bool -> m ()
solveSCCQuery globals useNewton = do
  let epsVar = actualEps globals
      eqs = eqMap globals

  currentEps <- liftIO $ readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  -- preprocess by propagating already known values
  solvedLVars <- preprocessApproxFixp eqs fst
  solvedUvars <- preprocessApproxFixp eqs snd
  let zipSolved = zip solvedLVars solvedUvars
      updatEqMap ((_, 0), (_, _)) = error "[Preprocessed equations] The equation system must be clean - please report this as a bug."
      updatEqMap ((_, _), (_, 0)) = error "[Preprocessed equations] The equation system must be clean - please report this as a bug."
      updatEqMap ((k1, l), (_, u)) = addFixpEq eqs k1 (PopEq (l,u))
  forM_ zipSolved updatEqMap

  unsolvedVars <- liveVariables eqs
  unless (V.null unsolvedVars) $ do
    let varSize = V.length unsolvedVars
    startWeights <- startTimer

    -- compute lower bounds
    approxVec <- if useNewton
      then approxFixpNewtonWithHint eqs fst (1000 * defaultEps) iterEps defaultMaxIters defaultMaxIters (V.replicate varSize 0)
      else approxFixpWithHint eqs fst iterEps defaultMaxIters (V.replicate varSize 0)

    -- compute upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system"
    oviRes <- ovi defaultOVISettingsDouble eqs snd approxVec
    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"

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
      when (u == 0 || l == 0) $ error "The equation system must be clean - please report this as a bug."
      addFixpEq eqs varKey (PopEq (l,u))) bounds