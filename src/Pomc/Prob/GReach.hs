{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Pomc.Prob.OVI (oviWithHints, oviToRationalWithHints, defaultOVISettingsDouble, OVIResult(..))

import Pomc.SatUtil

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM

import Pomc.IOSetMap (IOSetMap)
import qualified Pomc.IOSetMap as IOSM

import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM

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

import Data.IORef (IORef, newIORef, modifyIORef, modifyIORef', readIORef, modifyIORef')
import Data.Ratio (approxRational)

import Control.Applicative ((<|>))

-- import qualified Debug.Trace as DBG

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- global variables in the algorithms
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
    then return $ map (first getState) currentSuppEnds
    else do
      writeSTRef (currentInitial globals) (getId q)
      let newStateSatSet = PE.encodeSatState (proBitenc delta) state
      BH.insert (visited globals) (decode (q,Nothing)) newStateSatSet
      reach globals delta (q,Nothing) newStateSatSet
      updatedSuppEnds <- MM.lookup (suppEnds globals) (getId q)
      return $ map (first getState) updatedSuppEnds

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

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield && (consistentFilter delta) qState) =
            reachPush globals delta q g qState pathSatSet

        | precRel == Just Equal && (consistentFilter delta) qState =
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
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ map fst $ (deltaPush delta) qState
    mapM_ doPush newStates
    currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
    mapM_ (\(s, supportSatSet) -> reachTransition globals delta (Just pathSatSet) (Just supportSatSet) (s,g))
      currentSuppEnds

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
  let doPop p =
        let r = snd . fromJust $ g
            closeSupports g' = do
              lcSatSet <- fromJust <$> BH.lookup (visited globals) (decode (r,g'))
              reachTransition globals delta (Just lcSatSet) (Just pathSatSet) (p, g')
        in do
          MM.insertWith (suppEnds globals) (getId r) PE.union p pathSatSet
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ closeSupports currentSuppStarts
  in do
    newStates <- wrapStates (sIdGen globals) $ map fst $
      (deltaPop delta) qState (getState . snd . fromJust $ g)
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
  in do
  maybeSatSet <- BH.lookup (visited globals) (decode dest)
  if isNothing maybeSatSet
    then do
      -- dest semiconf has not been visited so far
      BH.insert (visited globals) (decode dest) newPathSatSet
      reach globals delta dest newPathSatSet
    else do
      let recordedSatSet = fromJust maybeSatSet
      let augmentedPathSatSet = PE.unions (recordedSatSet : catMaybes [pathSatSet, mSuppSatSet])
      unless (recordedSatSet `PE.subsumes` augmentedPathSatSet) $ do
        -- dest semiconf has been visited, but with a set of sat formulae that does not subsume the current ones
        BH.insert (visited globals) (decode dest) augmentedPathSatSet
        reach globals delta dest augmentedPathSatSet

--- compute weigths of a support transition
freezeSuppEnds :: GRobals RealWorld state -> IO (Vector (Set (StateId state)))
freezeSuppEnds globals = stToIO $ do
  computedSuppEnds <- readSTRef (suppEnds globals)
  V.generateM (MV.length computedSuppEnds) (fmap GeneralMap.keysSet . MV.unsafeRead computedSuppEnds)

type SuccessorsPopContexts = IntSet

data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , varMap     :: IORef (IOSetMap Int) -- variables associated with a semiconf
  , sStack     :: IOStack (StateId state, Stack state)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , successorsCntxs :: HT.BasicHashTable Int IntSet
  , upperEqMap :: EqMap EqMapNumbersType
  , lowerEqMap :: EqMap EqMapNumbersType
  , actualEps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

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
  let semiconf = (q, Nothing)
  targetState <- liftSTtoIO $ wrapState sIdGen target
  maybeSemiconfId <- liftIO $ HT.lookup (graphMap globals) (decode semiconf)

  actualId <- case maybeSemiconfId of
    Just scId -> do
      liftIO $ encodeInitialPush globals sIdGen delta q Nothing scId (getId targetState)
      solveSCCQuery (Set.singleton (scId, -1), IntSet.singleton scId) globals
      return scId
    Nothing -> do
      newId <- liftIO $ freshIOPosId (idSeq globals)
      liftIO $ HT.insert (graphMap globals) (decode semiconf) newId
      liftIO $ addtoPath globals semiconf newId
      _ <- dfs globals sIdGen delta supports semiconf (newId, getId targetState) True
      return newId

  -- returning the computed values
  eps <- liftIO $ readIORef (actualEps globals)
  lb <- liftIO $ (\(PopEq d) -> approxRational (d - eps) eps) . fromJust <$> HT.lookup (lowerEqMap globals) (actualId, -1)
  ub <- liftIO $ (\(PopEq d) -> approxRational (d + eps) eps) . fromJust <$> HT.lookup (upperEqMap globals) (actualId, -1)
  -- cleaning the hashtable
  liftIO $ HT.delete (lowerEqMap globals) (actualId, -1)
  liftIO $ HT.delete (upperEqMap globals) (actualId, -1)
  liftIO $ HT.delete (lowerEqMap globals) (-1, -1)
  liftIO $ HT.delete (upperEqMap globals) (-1, -1)
  logDebugN $ "Returning weights: " ++ show (lb, ub)
  when (lb > ub || lb > 1 || ub > 1.3) $ error "unsound bounds on weight for this summary transition"
  return (lb, ub)

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
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      transitionCases
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && not encodeNothing = return IntSet.empty

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield && (consistentFilter delta) qState) = do
          newPushStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaPush delta) qState
          forM_ newPushStates (\p -> follow (p, Just (qProps, q))) -- discard the result
          let newSupportStates = Set.toList $ fromJust $ (supports V.!? (getId q)) <|> (Just Set.empty)
          if isNothing g
            then return IntSet.empty
            else IntSet.unions <$> forM newSupportStates (\p -> follow (p, g))

        | precRel == Just Equal && (consistentFilter delta) qState = do
          newShiftStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaShift delta) qState
          IntSet.unions <$> forM newShiftStates (\p -> follow (p, Just (qProps, snd . fromJust $ g)))

        | precRel == Just Take = IntSet.fromList <$>
            mapM (\(unwrapped, _) -> do p <- liftSTtoIO $ wrapState sIdGen unwrapped; return (getId p)) ((deltaPop delta) qState (getState . snd . fromJust $ g))

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
    createComponent globals sIdGen delta supports (q,g) popContxs (semiconfId, target)

lookupVar :: (IORef (Set (Int,Int)), IntSet) -> WeightedGRobals state -> (Int, Int, Int) -> Int ->  IO (Maybe ((Int,Int), Bool))
lookupVar (newAdded, sccMembers) globals decoded rightContext = do
  maybeId <- HT.lookup (graphMap globals) decoded
  when (isNothing maybeId) $ error $ "future semiconfs should have been already visited and inserted in the hashtable: " ++ show decoded
  let id_ = fromJust maybeId
      varKey = (id_, rightContext)
      (_, a,b) = decoded
  when ((a,b) == (0,0) || rightContext == -1) $ error "semiconfs with empty stack should not be in the RHS of the equation system"
  previouslyVisited <- IOSM.member (varMap globals) id_ rightContext
  let cases
          | previouslyVisited = return $ Just (varKey, True)
          | IntSet.notMember id_ sccMembers = return Nothing
          | otherwise = do
              IOSM.insert (varMap globals) id_ rightContext
              modifyIORef' newAdded (Set.insert (id_,rightContext))
              return $ Just (varKey, False)
  cases

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
  -> (StateId state, Stack state)
  -> SuccessorsPopContexts
  -> (Int, Int)
  -> m SuccessorsPopContexts
createComponent globals sIdGen delta supports (q,g) popContxs (semiconfId, target) = do
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
        newAdded <- liftIO $ newIORef Set.empty
        let toEncode = [(s, semiconfId_, rc) | (s, semiconfId_) <- poppedSemiconfs, rc <- IntSet.toList popContxs]
            sccMembers = IntSet.fromList . map snd $ poppedSemiconfs
        insertedVars <- liftIO $ map (snd . fromJust) <$> forM toEncode (\(s, _, rc) -> lookupVar (newAdded, sccMembers) globals (decode s) rc)
        when (or insertedVars) $ error "inserting a variable that has already been encoded"
        liftIO $ forM_ toEncode $ \(s, _, rc) -> encode (newAdded, sccMembers) globals sIdGen delta supports s rc
        newAddedSet <- liftIO $ readIORef newAdded
        solveSCCQuery (newAddedSet, sccMembers) globals
        return popContxs
      doNotEncode poppedSemiconfs = do
        isInitial <- liftIO $ (== 0) <$> IOGS.size (sStack globals)
        when isInitial $ do -- for the initial semiconf, encode anyway
          liftIO $ encodeInitialPush globals sIdGen delta q g semiconfId target
          solveSCCQuery (Set.singleton (semiconfId, -1), IntSet.singleton semiconfId) globals
        return popContxs
      cases
        | iVal /= topB = return popContxs
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases


-- encode = generate the set of equation for pairs (semiconf, rightContext) to determine fraction f
encode :: (SatState state, Eq state, Hashable state, Show state)
  => (IORef (Set (Int,Int)), IntSet)
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> (StateId state, Stack state)
  -> Int
  -> IO ()
encode (newAdded, sccMembers) globals sIdGen delta supports (q,g) rightContext = do
  semiconfId <- fromJust <$> HT.lookup (graphMap globals) (decode (q,g))
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases

        | precRel == Just Yield =
            encodePush (newAdded, sccMembers) globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Equal =
            encodeShift (newAdded, sccMembers) globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Take = do
            distr <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (getId p, prob_)) $ (deltaPop delta) qState (getState . snd . fromJust $ g)
            let e = Map.findWithDefault 0 rightContext (Map.fromList distr)
            addFixpEq (lowerEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational e
            addFixpEq (upperEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational e
            -- logDebugN $ "Encoding PopSemiconf: " ++ show (semiconfId, rightContext) ++ " = PopEq " ++ show e

        | otherwise = fail "unexpected prec rel"
  cases

encodePush :: (SatState state, Eq state, Hashable state, Show state)
  => (IORef (Set (Int,Int)), IntSet)
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodePush (newAdded, sccMembers) globals sIdGen delta supports q g qState (semiconfId, rightContext) =
  let suppEnds = fromJust $ (supports V.!? getId q) <|> (Just Set.empty)
      qProps = getStateProps (bitenc delta) qState
      closeSupports pushDest (unencodedVars, terms) suppId =
        let suppDest = (suppId, g)
            varsList = [(pushDest, getId suppId), (suppDest, rightContext)]
        in do
          maybeTerms <- mapM (\(sc, rc) -> lookupVar (newAdded, sccMembers) globals (decode sc) rc) varsList
          let newUnencoded = [ semiconf | (semiconf, Just (_, False)) <- zip varsList maybeTerms]
                           ++ unencodedVars
          if any isNothing maybeTerms
            then return (newUnencoded, terms)
            else return (newUnencoded, map (fst . fromJust) maybeTerms:terms)

      pushEnc (newVars, terms) (p, prob_) =
        let dest = (p, Just (qProps, q)) in do
          (unencodedVars, varTerms) <- foldM (closeSupports dest) ([], []) suppEnds
          return (unencodedVars ++ newVars, (map (\[v1, v2] -> (prob_, v1, v2)) varTerms):terms)

  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
    (unencodedVars, terms) <- foldM pushEnc ([], []) newStates
    let emptyPush = all null terms
        pushEq | emptyPush = PopEq 0
               | otherwise = PushEq $ concat terms
    when emptyPush $ modifyIORef' newAdded (Set.delete (semiconfId, rightContext))
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) pushEq
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) pushEq
    -- logDebugN $ "Encoding Push: " ++ show terms
    forM_ unencodedVars $ \(sc, rc) -> encode (newAdded, sccMembers) globals sIdGen delta supports sc rc

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
            present <- IOSM.member (varMap globals) pushId suppId
            if present
              then return $ (prob_, (pushId, suppId), (-1, -1)):terms
              else return terms

    in do
      newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
      terms <- foldM pushEnc [] newStates
      addFixpEq (lowerEqMap globals) (semiconfId, -1) $ PushEq terms
      addFixpEq (upperEqMap globals) (semiconfId, -1) $ PushEq terms
      -- logDebugN $ "Encoding initial push:" ++ show terms
      addFixpEq (lowerEqMap globals) (-1, -1) $ PopEq (1 :: Double)
      addFixpEq (upperEqMap globals) (-1, -1) $ PopEq (1 :: Double)

encodeShift :: (SatState state, Eq state, Hashable state, Show state)
  => (IORef (Set (Int,Int)), IntSet)
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodeShift (newAdded, sccMembers) globals sIdGen delta supports _ g qState (semiconfId, rightContext) =
  let qProps = getStateProps (bitenc delta) qState
      shiftEnc (newVars, terms) (p, prob_) = do
        let dest = (p, Just (qProps, snd . fromJust $ g))
        maybeTerm <- lookupVar (newAdded, sccMembers) globals (decode dest) rightContext
        if isNothing maybeTerm
          then return (newVars, terms)
          else let 
            (varKey, alreadyEncoded) = fromJust maybeTerm
            newUnencoded = if alreadyEncoded then newVars else dest:newVars
          in return ( newUnencoded,(prob_, varKey):terms)
  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaShift delta) qState
    (unencodedVars, terms) <- foldM shiftEnc ([], []) newStates
    let shiftEq | null terms = error "shift semiconfs should go somewhere!"
                | otherwise = ShiftEq terms
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) shiftEq
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) shiftEq
    -- logDebugN $ "Encoding shift: " ++ show (semiconfId, rightContext) ++ " = ShiftEq " ++ show terms
    forM_ unencodedVars $ \sc -> encode (newAdded, sccMembers) globals sIdGen delta supports sc rightContext

solveSCCQuery :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
              => (Set (Int,Int), IntSet) -> WeightedGRobals state -> m ()
solveSCCQuery (newAdded, sccMembers) globals = do
  let variables = Set.toList newAdded
      sccLen = IntSet.size sccMembers
      epsVar = actualEps globals
      lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals

  currentEps <- liftIO $ readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  -- preprocessing to solve variables that do not need ovi
  _ <- preprocessApproxFixpWithHints lEqMap iterEps (2 * sccLen) variables
  (_, unsolvedVars) <- preprocessApproxFixpWithHints uEqMap iterEps (2 * sccLen) variables

  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCountQuant = acc} -> s{largestSCCSemiconfsCountQuant = max acc (IntSet.size sccMembers)}

  -- lEqMap and uEqMap should be the same here
  unless (null unsolvedVars) $ do
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquationsQuant = acc} -> s{nonTrivialEquationsQuant = acc + length unsolvedVars}
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCEqsCountQuant = acc } -> s{ largestSCCEqsCountQuant = max acc (length unsolvedVars) }
    startWeights <- startTimer

    logInfoN "Running OVI to solve the equation system"
    oviRes <- oviWithHints defaultOVISettingsDouble uEqMap unsolvedVars

    rCertified <- oviToRationalWithHints defaultOVISettingsDouble uEqMap oviRes unsolvedVars
    unless rCertified $ error "cannot deduce a rational certificate for this SCC when computing fraction f"

    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"

    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { quantWeightTime = quantWeightTime s + tWeights })

    -- updating lower bounds
    approxVec <- approxFixpWithHints lEqMap iterEps defaultMaxIters unsolvedVars
    forM_ unsolvedVars $ \varKey -> liftIO $ do
      HT.lookup lEqMap varKey >>= \case
          Just (PopEq _) -> error "trying to update a dead variable"
          _ -> do
            p <- fromJust <$> HT.lookup approxVec varKey
            addFixpEq lEqMap varKey (PopEq p)

    -- updating upper bounds
    upperBound <- liftIO $ foldM (\acc varKey -> HT.lookup uEqMap varKey >>= \case
          Just (PopEq _) -> error "trying to update a variable that is already dead"
          _ -> do
            p <- fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
            addFixpEq uEqMap varKey (PopEq p)
            return ((varKey, p): acc))
      [] unsolvedVars

    logInfoN $ "Computed upper bounds: " ++ show upperBound
