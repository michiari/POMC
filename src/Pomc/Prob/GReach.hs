{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.GReach
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( GRobals(..)
                        , Delta(..)
                        , WeightedGRobals(..)
                        , newGRobals
                        , reachableStates
                        , showGrobals
                        , weightQuerySCC
                        , freezeSuppEnds
                        ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType, Stats(..))
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
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

import qualified Data.IntMap as Map


import qualified Data.Map as GeneralMap

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

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- global variables for detecting reachable right contexts of supports edges in graph G
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
        | (isNothing g) && (getId q /= i) = do
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push with empty stack in GReach " ++  show qState

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield ) = do
            -- sanity check
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push in GReach " ++  show qState ++ "; " ++ show g ++ ";\n\n\nPREC " ++ show precRel
            reachPush globals delta q g qState pathSatSet

        | precRel == Just Equal = do
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a shift in GReach " ++  show qState
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
  in do
    newStates <- wrapStates (sIdGen globals) $ map fst $ (deltaShift delta) qState
    mapM_ doShift newStates

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
  in do
    newStates <- wrapStates (sIdGen globals) $ map fst $
      (deltaPop delta) qState gState
    mapM_  doPop newStates

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

freezeSuppEnds :: GRobals RealWorld state -> IO (Vector (Set (StateId state)))
freezeSuppEnds globals = stToIO $ do
  computedSuppEnds <- readSTRef (suppEnds globals)
  V.generateM (MV.length computedSuppEnds) (fmap GeneralMap.keysSet . MV.unsafeRead computedSuppEnds)

type SuccessorsPopContexts = IntSet

data QuantVariable state = QuantVariable (StateId state, Stack state) (Int, Int)

instance Eq (QuantVariable state) where
  (QuantVariable _ a) == (QuantVariable _ b) = a == b

instance Ord (QuantVariable state) where
  compare (QuantVariable _ a) (QuantVariable _ b) = compare a b

-- global variables for computing weights of support edges in graph H 
-- with respect to the prob. of the support transition in the support chain
data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , sStack     :: IOStack (StateId state, Stack state)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , successorsCntxs :: HT.BasicHashTable Int IntSet
  , eqMap :: AugEqMap (EqMapNumbersType,EqMapNumbersType)
  , actualEps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

-- compute weigths of a support edge in H with respect to the support transition
weightQuerySCC :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
               => WeightedGRobals state
               -> SIdGen RealWorld state
               -> Delta state -- delta relation of the augmented opa
               -> Vector (Set(StateId state))
               -> state -- current state
               -> state -- target state
               -> m (Prob, Prob)
weightQuerySCC globals sIdGen delta supports current target = do
  q <- liftSTtoIO $ wrapState sIdGen current
  targetState <- liftSTtoIO $ wrapState sIdGen target
  let semiconf = (q, Nothing)
      decodedSemiconf = decode semiconf
      targetId = getId targetState
  maybeSemiconfId <- liftIO $ HT.lookup (graphMap globals) decodedSemiconf

  actualId <- case maybeSemiconfId of
    Just scId -> do
      liftIO $ encodeInitialPush globals sIdGen delta q Nothing scId targetId
      solveSCCQuery (IntSet.singleton scId) globals
      return scId
    Nothing -> do
      newId <- liftIO $ freshIOPosId (idSeq globals)
      liftIO $ HT.insert (graphMap globals) decodedSemiconf newId
      liftIO $ addtoPath globals semiconf newId
      _ <- dfs globals sIdGen delta supports semiconf (newId, targetId) True
      liftIO $ encodeInitialPush globals sIdGen delta q Nothing newId targetId
      solveSCCQuery (IntSet.singleton newId) globals
      return newId

  -- returning the computed values
  eps <- liftIO $ readIORef (actualEps globals)
  (lb, ub) <- liftIO $ (\(PopEq (d, c)) -> (approxRational (d - eps) eps, approxRational (c - eps) eps)) . fromJust <$> IOMM.lookupValue (fst $ eqMap globals) actualId (-1)
  -- cleaning the hashtable
  deleteFixpEq (eqMap globals) (actualId, -1)
  deleteFixpEq (eqMap globals) (actualId, -2)
  let truncatedLB = min 1 lb
      truncatedUB = min 1 ub

  logInfoN $ "Returning weights: " ++ show (truncatedLB, truncatedUB)
  when (lb > ub || lb > 1 || ub - lb > 1 % 50) $ error $ "unsound or too loose bounds on weights for this summary transition: " ++ show (lb,ub)
  return (truncatedLB, truncatedUB)

-- functions for Gabow algorithm
dfs :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> Vector (Set(StateId state))
    -> (StateId state, Stack state) -- current semiconf
    -> (Int, Int) -- target
    -> Bool
    -> m SuccessorsPopContexts
dfs globals sIdGen delta supports (q,g) (semiconfId, target) encodeNothing =
  let qState = getState q
      gState = getState . snd . fromJust $ g
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      transitionCases
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && not encodeNothing = do
          unless ((consistentFilter delta) qState) $ error "semiconfigurations with empty stack but inconsistent states"
          return IntSet.empty

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield = do
          unless ((consistentFilter delta) qState) $ error "inconsistent state in a push"
          newPushStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaPush delta) qState
          forM_ newPushStates (\p -> follow (p, Just (qProps, q))) -- discard the result
          let isConsistentOrPop p = let s = getState p in
                (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) s) == Just Take)
                || (consistentFilter delta) s
              newSupportStates = Set.toList . Set.filter isConsistentOrPop . fromJust $ (supports V.!? (getId q)) <|> Just Set.empty
          if isNothing g
            then return IntSet.empty
            else IntSet.unions <$> forM newSupportStates (\p -> follow (p, g))

        | precRel == Just Equal = do
          unless ((consistentFilter delta) qState) $ error "inconsistent state in a push"
          newShiftStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaShift delta) qState
          IntSet.unions <$> forM newShiftStates (\p -> follow (p, Just (qProps, snd . fromJust $ g)))

        | precRel == Just Take = IntSet.fromList <$>
            mapM (\(unwrapped, _) -> getId <$> liftSTtoIO (wrapState sIdGen unwrapped)) ((deltaPop delta) qState gState)

        | otherwise = return IntSet.empty

      cases nextSemiconf nSCId iVal
        | (iVal == 0) = do
            liftIO $ addtoPath globals nextSemiconf nSCId
            dfs globals sIdGen delta supports nextSemiconf (nSCId, target) False
        | (iVal < 0)  = liftIO $ lookupCntxs globals nSCId
        | (iVal > 0)  = liftIO $ merge globals nextSemiconf nSCId >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow nextSemiconf = do
        nSCId <- liftIO $ lookupSemiconf globals nextSemiconf
        iVal <- liftIO $ lookupIValue globals nSCId
        cases nextSemiconf nSCId iVal

  in do
    popContxs <- transitionCases
    createComponent globals sIdGen delta supports popContxs semiconfId

lookupIValue :: WeightedGRobals state -> Int -> IO Int
lookupIValue globals semiconfId = do
  maybeIval <- HT.lookup (iVector globals) semiconfId
  maybe (return 0) return maybeIval

lookupCntxs :: WeightedGRobals state -> Int -> IO IntSet
lookupCntxs globals semiconfId = do
    maybeCntxs <- HT.lookup (successorsCntxs globals) semiconfId
    maybe (return IntSet.empty) return maybeCntxs

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

addtoPath :: WeightedGRobals state -> (StateId state, Stack state) -> Int -> IO ()
addtoPath globals semiconf semiconfId = do
  IOGS.push (sStack globals) semiconf
  sSize <- IOGS.size $ sStack globals
  HT.insert (iVector globals) semiconfId sSize
  IOGS.push (bStack globals) sSize

merge ::  WeightedGRobals state -> (StateId state, Stack state) -> Int -> IO ()
merge globals _ semiconfId = do
  iVal <- lookupIValue globals semiconfId
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

createComponent :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> SuccessorsPopContexts
  -> Int
  -> m SuccessorsPopContexts
createComponent globals sIdGen delta supports popContxs semiconfId = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ lookupIValue globals semiconfId
  let createC = liftIO $ do
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        forM poppedSemiconfs $ \s -> do
          actualId <- fromJust <$> HT.lookup (graphMap globals) (decode s)
          HT.insert (iVector globals) actualId (-1)
          HT.insert (successorsCntxs globals) actualId popContxs
          return (s, actualId)
      doEncode poppedSemiconfs = do
        let toEncode = [QuantVariable s (semiconfId_, rc) | (s, semiconfId_) <- poppedSemiconfs, rc <- IntSet.toList popContxs]
            toEncodeSet = Set.fromList toEncode
            sccMembers = IntSet.fromList . map snd $ poppedSemiconfs
        liftIO $ do
          -- this sanity check has been removed for performance reasons
          -- insertedVars <- map (snd . fromJust) <$> forM toEncode (\(s, _, rc) -> lookupVar sccMembers globals (decode s) rc)
          -- when (or insertedVars) $ error "inserting a variable that has already been encoded"
          -- little optimization trick
          forM_ toEncode (\ (QuantVariable _ varKey) -> addFixpEq (eqMap globals) varKey (PushEq []))
          encode toEncodeSet globals sIdGen delta supports sccMembers

        solveSCCQuery sccMembers globals
        return popContxs
      doNotEncode _ = do
          liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
          return popContxs
      cases
        | iVal /= topB = return popContxs
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases


-- encode = generate the set of equation for pairs (semiconf, rightContext) to determine fraction f
encode :: (SatState state, Eq state, Hashable state, Show state)
  => Set (QuantVariable state)
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> IntSet
  -> IO ()
encode unencodedVars globals sIdGen delta supports sccMembers
  | Set.null unencodedVars = return ()
  | otherwise =
    let (QuantVariable (q,g) varKey, othersUnencoded) = Set.deleteFindMin unencodedVars
        qState = getState q
        gState = getState . snd . fromJust $ g
        qProps = getStateProps (bitenc delta) qState
        precRel = (prec delta) (fst . fromJust $ g) qProps
        cases
          | precRel == Just Yield =
              encodePush globals sIdGen delta supports q g qState varKey sccMembers

          | precRel == Just Equal =
              encodeShift globals sIdGen delta q g qState varKey sccMembers

          | precRel == Just Take = do
              distr <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (getId p, prob_)) $ (deltaPop delta) qState gState
              let e = Map.findWithDefault 0 (snd varKey) (Map.fromList distr)
              addFixpEq (eqMap globals) varKey $ PopEq $ (fromRational e, fromRational e)
              liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
              return Set.empty
              -- logDebugN $ "Encoding PopSemiconf: " ++ show varKey ++ " = PopEq " ++ show e

          | otherwise = fail "unexpected prec rel"
    in do
      newUnencoded <- cases
      encode (Set.union othersUnencoded newUnencoded) globals sIdGen delta supports sccMembers


encodePush :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IntSet
  -> IO (Set (QuantVariable state))
encodePush globals sIdGen delta supports q g qState (semiconfId, rightContext) sccMembers =
  let isConsistentOrPop p = let s = getState p in
        (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) s) == Just Take)
        || (consistentFilter delta) s
      (a,b) = decodeStack g -- current stack decoded 
      qProps = getStateProps (bitenc delta) qState
      newG = Just (qProps, q)
      (c,d) = decodeStack newG
      suppEnds = Set.toList . Set.filter isConsistentOrPop . fromJust $ (supports V.!? getId q) <|> (Just Set.empty)
      suppEndsIds = map decodeStateId suppEnds
      suppDecodedSemiconfs = map (, a, b) suppEndsIds

  in do
    newStates <- mapM (\(unwrapped, prob_) -> (,prob_) <$> stToIO (wrapState sIdGen unwrapped)) $ (deltaPush delta) qState
    suppSemiconfsIds <- mapM (fmap fromJust . HT.lookup (graphMap globals)) suppDecodedSemiconfs
    newUnencoded <- newIORef Set.empty

    let suppInfo = zip3 suppEnds suppEndsIds (map (, rightContext) suppSemiconfsIds)
    suppVarKeys  <- foldM (\acc (s, sId, varKey) -> do
      previouslyEncoded <- containsEquation (eqMap globals) varKey
      let quantVar = QuantVariable (s, g) varKey
          cases
            | previouslyEncoded = return $ (sId, varKey):acc
            | IntSet.notMember (fst varKey) sccMembers = return acc
            | otherwise = do
              addFixpEq (eqMap globals) varKey (PushEq [])
              modifyIORef' newUnencoded $ Set.insert quantVar
              return $ (sId, varKey):acc
      cases
      ) [] suppInfo

    let newStatesWithSuppIds = [(p, prob_, suppRC) | (p,prob_) <- newStates, suppRC <- suppEndsIds]
    pushVarKeys <- foldM (\acc (p, prob_, suppRC) -> do
      let decoded = (decodeStateId p, c, d)
      id_ <- fromJust <$> HT.lookup (graphMap globals) decoded
      let varKey = (id_, suppRC)
      previouslyEncoded <- containsEquation (eqMap globals) varKey
      let quantVar = QuantVariable (p, newG) varKey
          cases
            | previouslyEncoded = return $ (prob_, varKey):acc
            | IntSet.notMember id_ sccMembers = return acc
            | otherwise = do
              addFixpEq (eqMap globals) varKey (PushEq [])
              modifyIORef' newUnencoded $ Set.insert quantVar
              return $ (prob_, varKey):acc
      cases
      ) [] newStatesWithSuppIds

    let terms = [(prob_, pushVarKey, suppVarKey) |
                  (suppSId, suppVarKey) <- suppVarKeys,
                  (prob_, pushVarKey) <- pushVarKeys,
                  snd pushVarKey == suppSId
                ]
        pushEq | null terms = PopEq (0, 0)
               | otherwise = PushEq terms
    addFixpEq (eqMap globals) (semiconfId, rightContext) pushEq
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
    readIORef newUnencoded

encodeInitialPush :: (SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> StateId state
    -> Stack state
    -> Int
    -> Int
    -> IO ()
encodeInitialPush globals sIdGen delta q _ semiconfId suppId  =
    let qState = getState q
        qProps = getStateProps (bitenc delta) qState
        pushEnc terms (p, prob_) =
          let dest = (p, Just (qProps, q)) in do
            pushId <- fromJust <$> HT.lookup (graphMap globals) (decode dest)
            present <- containsEquation (eqMap globals) (pushId, suppId)
            if present
              then return $ (prob_, (pushId, suppId), (semiconfId, -2)):terms
              else return terms
    in do
      newStates <- mapM (\(unwrapped, prob_) -> (,prob_) <$> stToIO (wrapState sIdGen unwrapped)) $ (deltaPush delta) qState
      terms <- foldM pushEnc [] newStates
      addFixpEq (eqMap globals) (semiconfId, -1) $ PushEq terms
      -- logDebugN $ "Encoding initial push:" ++ show terms
      addFixpEq (eqMap globals) (semiconfId, -2) $ PopEq (1,1)
      liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}

encodeShift :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IntSet
  -> IO (Set (QuantVariable state))
encodeShift globals sIdGen delta _ g qState fromVarKey sccMembers =
  let qProps = getStateProps (bitenc delta) qState
      shiftEnc (newVars, terms) (p, prob_) = do
        let dest = (p, Just (qProps, snd . fromJust $ g))
            decoded = decode dest
        id_ <- fromJust <$> HT.lookup (graphMap globals) decoded
        let varKey = (id_, snd fromVarKey)
        previouslyEncoded <- containsEquation (eqMap globals) varKey
        let cases
              | previouslyEncoded = return (newVars, (prob_, varKey):terms)
              | IntSet.notMember id_ sccMembers = return (newVars, terms)
              | otherwise = do 
                addFixpEq (eqMap globals) varKey (PushEq [])
                return ( Set.insert (QuantVariable dest varKey) newVars,
                  (prob_, varKey):terms)
        cases
  in do
    newStates <- mapM (\(unwrapped, prob_) -> (,prob_) <$> stToIO (wrapState sIdGen unwrapped)) $ (deltaShift delta) qState
    (unencodedVars, terms) <- foldM shiftEnc (Set.empty, []) newStates
    let shiftEq | null terms = error "shift semiconfs should go somewhere!"
                | otherwise = ShiftEq terms
    addFixpEq (eqMap globals) fromVarKey shiftEq
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
    -- logDebugN $ "Encoding shift: " ++ show fromVarKey ++ " = ShiftEq " ++ show terms
    return unencodedVars

solveSCCQuery :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
              => IntSet -> WeightedGRobals state -> m ()
solveSCCQuery sccMembers globals = do
  let sccLen = IntSet.size sccMembers
      epsVar = actualEps globals
      eqs = eqMap globals

  currentEps <- liftIO $ readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  -- preprocessing to solve variables that do not need ovi
  (solvedLVars, _) <- preprocessApproxFixp eqs fst iterEps (sccLen + 1)
  (solvedUvars, unsolvedVars) <- preprocessApproxFixp eqs snd iterEps (sccLen + 1)

  let zipSolved = zip solvedLVars solvedUvars
  liftIO $ forM_ zipSolved $ \((k1, l), (_, u)) -> do
    addFixpEq eqs k1 (PopEq (l,u))

  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCountQuant = acc} -> s{largestSCCSemiconfsCountQuant = max acc (IntSet.size sccMembers)}

  unless (null unsolvedVars) $ do
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquationsCountQuant = acc} -> s{nonTrivialEquationsCountQuant = acc + length unsolvedVars}
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCNonTrivialEqsCountQuant = acc } -> s{ largestSCCNonTrivialEqsCountQuant = max acc (length unsolvedVars) }
    startWeights <- startTimer

    -- compute lower bounds
    approxVec <- approxFixp eqs fst iterEps defaultMaxIters

    -- compute upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system"
    oviRes <- ovi defaultOVISettingsDouble eqs snd

    -- certify the result and compute some statistics
    rCertified <- oviToRational defaultOVISettingsDouble eqs snd oviRes
    unless rCertified $ error "cannot deduce a rational certificate for this SCC when computing fraction f"
    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"
    logDebugN $ "Computed upper bounds: " ++ show (oviUpperBound oviRes)
    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { quantWeightTime = quantWeightTime s + tWeights })

    -- updating lower and upper bounds 
    let bounds = V.zip approxVec (oviUpperBound oviRes)
    V.mapM_ (\((k1, l), (_, u)) -> do
      addFixpEq eqs k1 (PopEq (l,u))) bounds