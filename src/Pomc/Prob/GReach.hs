{- |
   Module      : Pomc.GReach
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
{-# LANGUAGE LambdaCase #-}

module Pomc.Prob.GReach ( GRobals(..)
                        , Delta(..)
                        , WeightedGRobals(..)
                        , newGRobals
                        , reachableStates
                        , showGrobals
                        , weightQuerySCC
                        , freezeSuppEnds
                        ) where
import Pomc.Prob.ProbUtils(Prob, EqMapNumbersType, defaultTolerance)
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
import qualified Pomc.Prob.ProbEncoding as PE

import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))

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

import Data.IntMap(IntMap)
import qualified Data.IntMap as Map

import Data.Map(Map)
import qualified Data.Map as GeneralMap

import Data.Vector(Vector)
import qualified Data.Vector as V

import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad.ST (ST, RealWorld)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef)

import Control.Monad(unless, when, foldM, forM_, forM)

import Data.Maybe
import Data.Hashable(Hashable)

import Data.Bifunctor(first)

import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as BC
import qualified Data.HashTable.IO as HT

import qualified Data.Vector.Mutable as MV
import GHC.IO (stToIO)

import Data.IORef (IORef, newIORef, modifyIORef, readIORef, writeIORef, modifyIORef')
import Data.Ratio (approxRational)

import qualified Debug.Trace as DBG

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

newGRobals ::  ST.ST s (GRobals s state)
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
  V.generateM (MV.length computedSuppEnds) (\idx -> GeneralMap.keysSet <$> MV.unsafeRead computedSuppEnds idx)

type SuccessorsPopContexts = IntSet

data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , varMap     :: IORef (IOSetMap Int) -- variables associated with a semiconf
  , sStack     :: IOStack (StateId state, Stack state)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , successorsCntxs :: HT.BasicHashTable Int IntSet
  , cannotReachPop :: IORef IntSet
  , upperEqMap :: EqMap EqMapNumbersType
  , lowerEqMap :: EqMap EqMapNumbersType
  , actualEps :: IORef EqMapNumbersType
  }

weightQuerySCC :: (SatState state, Eq state, Hashable state, Show state)
                 => SIdGen RealWorld state
                 -> Delta state -- delta relation of the augmented opa
                 -> Vector (Set(StateId state))
                 -> state -- current state
                 -> state -- target state
                 -> IO (Prob, Prob)
weightQuerySCC sIdGen delta supports current target = do
  q <- stToIO $ wrapState sIdGen current
  let semiconf = (q, Nothing)
  newIdSeq <- newIORef 0
  newGraphMap <-  HT.new
  newFVarMap <- IOSM.empty
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVector <- HT.new
  newScntxs <- HT.new
  newCannotReachPop <- newIORef IntSet.empty
  newLowerEqMap <- HT.new
  newUpperEqMap <- HT.new
  newEps <- newIORef defaultTolerance

  let globals = WeightedGRobals { idSeq = newIdSeq
                                , graphMap = newGraphMap
                                , varMap  = newFVarMap
                                , sStack = newSStack
                                , bStack = newBStack
                                , iVector = newIVector
                                , successorsCntxs = newScntxs
                                , cannotReachPop = newCannotReachPop
                                , lowerEqMap = newLowerEqMap
                                , upperEqMap = newUpperEqMap
                                , actualEps = newEps
                                  }
  newId <- freshIOPosId (idSeq globals)
  HT.insert (graphMap globals) (decode semiconf) newId
  targetState <- stToIO $ wrapState sIdGen target
  addtoPath globals semiconf newId >> dfs globals sIdGen delta supports semiconf (newId, getId targetState) True >> return ()

  --DBG.traceM $ "Target state: " ++ show targetState
  -- returning the computed values
  eps <- readIORef (actualEps globals)
  lb <- (\(PopEq d) -> approxRational (d - eps) eps) . fromJust <$> HT.lookup (lowerEqMap globals) (newId, -1)
  ub <- (\(PopEq d) -> approxRational (d + eps) eps) . fromJust <$> HT.lookup (upperEqMap globals) (newId, -1)
  return (lb, ub)


lookupVar :: IORef (Set (Int,Int)) -> WeightedGRobals state -> (Int, Int, Int) -> Int ->  IO ((Int,Int), Bool)
lookupVar newAdded globals decoded rightContext = do
  maybeId <- HT.lookup (graphMap globals) decoded
  when (isNothing maybeId) $ error "future semiconfs should have been already visited and inserted in the hashtable"
  let id_ = fromJust maybeId
      key = (id_, rightContext)
      (_, a,b) = decoded
  when ((a,b) == (0,0) || rightContext == -1) $ error "semiconfs with empty stack should not be in the RHS of the equation system"
  asPendingIdxes <- readIORef (cannotReachPop globals)
  if IntSet.member id_ asPendingIdxes
      then do
        addFixpEq (lowerEqMap globals) key (PopEq 0)
        addFixpEq (upperEqMap globals) key (PopEq 0)
        return (key, True)
        else do
            previouslyVisited <- IOSM.member (varMap globals) id_ rightContext
            if previouslyVisited
              then return (key, True)
              else do
                IOSM.insert (varMap globals) id_ rightContext
                modifyIORef' newAdded (Set.insert (id_,rightContext))
                return (key, False)

-- functions for Gabow algorithm
dfs :: (SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> Vector (Set(StateId state))
    -> (StateId state, Stack state) -- current semiconf
    -> (Int, Int) -- target
    -> Bool
    -> IO SuccessorsPopContexts
dfs globals sIdGen delta supports (q,g) (semiconfId, target) encodeNothing =
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      transitionCases
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && not encodeNothing = return IntSet.empty

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield && (consistentFilter delta) qState) = do
          let newSupportStates = Set.toList $ supports V.! (getId q)
          popContexts <- IntSet.unions <$> forM newSupportStates (\p -> follow (p, g)) -- discard the result
          newPushStates <- stToIO $ wrapStates sIdGen $ map fst $ (deltaPush delta) qState
          forM_ newPushStates (\p -> follow (p, Just (qProps, q))) -- discard the result
          return popContexts

        | precRel == Just Equal && (consistentFilter delta) qState = do
          newShiftStates <- stToIO $ wrapStates sIdGen $ map fst $ (deltaShift delta) qState
          IntSet.unions <$> forM newShiftStates (\p -> follow (p, Just (qProps, snd . fromJust $ g)))

        | precRel == Just Take = do
            newPopStates <- stToIO $ wrapStates sIdGen  $ map fst $ (deltaPop delta) qState (getState . snd . fromJust $ g)
            return $ IntSet.fromList (map getId (V.toList newPopStates))

        | otherwise = return IntSet.empty

      cases nextSemiconf nSCId iVal
        | (iVal == 0) = addtoPath globals nextSemiconf nSCId >> dfs globals sIdGen delta supports nextSemiconf (nSCId, target) False
        | (iVal < 0)  = lookupCntxs globals nSCId
        | (iVal > 0)  = merge globals nextSemiconf nSCId >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow nextSemiconf = do
        nSCId <- lookupSemiconf globals nextSemiconf
        iVal <- lookupIValue globals nSCId
        cases nextSemiconf nSCId iVal

  in do
    popContxs <- transitionCases
    --DBG.traceM $ "Creating component for semiconf: " ++ show (q,g)
    createComponent globals sIdGen delta supports (q,g) popContxs (semiconfId, target)

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

createComponent :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> (StateId state, Stack state)
  -> SuccessorsPopContexts
  -> (Int, Int)
  -> IO SuccessorsPopContexts
createComponent globals sIdGen delta supports (q,g) popContxs (semiconfId, target) = do
  topB <- IOGS.peek $ bStack globals
  iVal <- lookupIValue globals semiconfId
  let createC = do
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        --DBG.traceM $ "Pop contexts: " ++ show popContxs
        forM poppedSemiconfs $ \s -> do
          actualId <- fromJust <$> HT.lookup (graphMap globals) (decode s)
          HT.insert (iVector globals) actualId (-1)
          HT.insert (successorsCntxs globals) actualId popContxs
          return (s, actualId)
      doEncode poppedSemiconfs = do  
        --DBG.traceM  $ "Popped Semiconfigurations: " ++ show (poppedSemiconfs)   
        --DBG.traceM $ "Encode!"
        newAdded <- newIORef Set.empty
        let to_be_encoded = [(s, semiconfId_, rc) | (s, semiconfId_) <- poppedSemiconfs, rc <- IntSet.toList popContxs]
        insertedVars <- map snd <$> forM to_be_encoded (\(s, _, rc) -> lookupVar newAdded globals (decode s) rc)
        when (or insertedVars) $ error "inserting a variable that has already been encoded"
        forM_ to_be_encoded $ \(s, _, rc) -> encode newAdded globals sIdGen delta supports s rc
        newAddedSet <- readIORef newAdded
        solveSCCQuery (map snd poppedSemiconfs) newAddedSet globals
        return popContxs
      doNotEncode poppedSemiconfs = do
        --DBG.traceM  $ "Popped Semiconfigurations: " ++ show (map snd poppedSemiconfs)   
        --DBG.traceM $ "Do not encode!"
        modifyIORef (cannotReachPop globals) $ IntSet.union (IntSet.fromList $ map snd poppedSemiconfs)
        isInitial <- (== 0) <$> IOGS.size (sStack globals)
        when isInitial $ do -- for the initial semiconf, encode anyway
          newAdded <- newIORef Set.empty
          encodeInitialPush newAdded globals sIdGen delta supports q g semiconfId target
          modifyIORef newAdded (Set.insert (semiconfId, -1))
          newAddedSet <- readIORef newAdded
          solveSCCQuery (map snd poppedSemiconfs) newAddedSet globals
        return popContxs
      cases
        | iVal /= topB = --DBG.traceM "not bottom of the SCC - return as it is" >> 
          return popContxs
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases


-- encode = generate the set of equation for pairs (semiconf, rightContext) to determine fraction f
encode :: (SatState state, Eq state, Hashable state, Show state)
  => IORef (Set (Int,Int))
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> (StateId state, Stack state)
  -> Int
  -> IO ()
encode newAdded globals sIdGen delta supports (q,g) rightContext = do
  semiconfId <- fromJust <$> HT.lookup (graphMap globals) (decode (q,g))
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases

        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush newAdded globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Equal =
            encodeShift newAdded globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Take = do
            --when (rightContext < 0) $ error $ "Reached a pop with unconsistent left context: "
            popDistribution <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (getId p,prob_)) $ (deltaPop delta) qState (getState . snd . fromJust $ g)
            let prob_ = Map.findWithDefault 0 rightContext $ Map.fromList popDistribution
            --DBG.traceM $ "Encoding pop semiconf to rightContext: " ++ show rightContext ++ " - with prob " ++ show prob_
            addFixpEq (lowerEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational prob_
            addFixpEq (upperEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational prob_


        | otherwise = fail "unexpected prec rel"
  --DBG.traceM $ "Encoding semiconf: " ++ show (q,g) ++ " - with right context: " ++ show rightContext
  cases

encodePush :: (SatState state, Eq state, Hashable state, Show state)
  => IORef (Set (Int,Int))
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodePush newAdded globals sIdGen delta supports q g qState (semiconfId, rightContext) =
  let suppEnds = supports V.! getId q
      qProps = getStateProps (bitenc delta) qState
      recurse (dest, rc) = encode newAdded globals sIdGen delta supports dest rc
      closeSupports pushDest (unencodedSCs, terms) suppId =
        let suppDest = (suppId, g) in do
        vars <- mapM (uncurry (lookupVar newAdded globals)) [(decode pushDest, getId suppId), (decode suppDest, rightContext)]
        return ( (map fst . filter snd $ zip [(pushDest, getId suppId), (suppDest, rightContext)] (map snd vars)) ++ unencodedSCs
          , (map fst vars):terms
          )
      pushEnc (newSCs, terms) (p, prob_) =
        let dest = (p, Just (qProps, q)) in do
          (unencodedSCs, pushTerms) <- foldM (closeSupports dest) ([], []) suppEnds
          return ( unencodedSCs ++ newSCs
                , (map (\[v1, v2] -> (prob_, v1, v2)) pushTerms):terms
                )

  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
    (unencodedSCs, terms) <- foldM pushEnc ([], []) newStates
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) $ PushEq $ concat terms
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) $ PushEq $ concat terms
    --DBG.traceM $ "Encoding push: " ++ show (concat terms)
    mapM_ recurse unencodedSCs

encodeInitialPush :: (SatState state, Eq state, Hashable state, Show state)
    => IORef (Set (Int,Int))
    -> WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> Vector (Set(StateId state))
    -> StateId state
    -> Stack state
    -> Int
    -> Int
    -> IO ()
encodeInitialPush newAdded globals sIdGen delta supports q _ semiconfId suppId =
    let qState = getState q
        qProps = getStateProps (bitenc delta) qState
        recurse dest = encode newAdded globals sIdGen delta supports dest suppId
        pushEnc (newSCs, terms) (p, prob_) =
          let dest = (p, Just (qProps, q)) in do
            (key, alreadyEncoded) <- lookupVar newAdded globals (decode dest) suppId
            return ( if alreadyEncoded then newSCs else dest:newSCs
                  , (prob_, key, (suppId, -1)):terms
                  )

    in do
      newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
      (unencodedSCs, terms) <- foldM pushEnc ([], []) newStates
      addFixpEq (lowerEqMap globals) (semiconfId, -1) $ PushEq terms
      addFixpEq (upperEqMap globals) (semiconfId, -1) $ PushEq terms
      --DBG.traceM $ "Encoding initial push: " ++ show terms
      addFixpEq (lowerEqMap globals) (suppId, -1) $ PopEq (1 :: Double)
      addFixpEq (upperEqMap globals) (suppId, -1) $ PopEq (1 :: Double)
      mapM_ recurse unencodedSCs

encodeShift :: (SatState state, Eq state, Hashable state, Show state)
  => IORef (Set (Int,Int))
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodeShift newAdded globals sIdGen delta supports _ g qState (semiconfId, rightContext) =
  let qProps = getStateProps (bitenc delta) qState
      recurse dest = encode newAdded globals sIdGen delta supports dest rightContext
      shiftEnc (newSCs, terms) (p, prob_) = do
        let dest = (p, Just (qProps, snd . fromJust $ g))
        (key, alreadyEncoded) <- lookupVar newAdded globals (decode dest) rightContext
        return ( if alreadyEncoded then newSCs else dest:newSCs
                , (prob_, key):terms
                )
  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaShift delta) qState
    (unencodedSCs, terms) <- foldM shiftEnc ([], []) newStates
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) $ ShiftEq terms
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) $ ShiftEq terms
    --DBG.traceM $ "Encoding shift: " ++ show terms
    mapM_ recurse unencodedSCs



solveSCCQuery :: (Eq state, Hashable state, Show state)
  => [Int] -> Set (Int,Int) -> WeightedGRobals state -> IO ()
solveSCCQuery sccMembers newAdded globals = do
  --DBG.traceM "Assert hints to solve the query"
  let variables = Set.toList newAdded
      sccLen = length sccMembers
      epsVar = actualEps globals
      lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals

  currentEps <- readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  --eqMapList <- liftIO $ HT.toList eMap
  --DBG.traceM $ "Current equation system: \n" ++ concatMap (\l -> show l ++ "\n") eqMapList

  -- preprocessing to solve variables that do not need ovi
  _ <- preprocessApproxFixp lEqMap iterEps (2 * sccLen)
  _ <- preprocessApproxFixp uEqMap iterEps (2 * sccLen)


  oviRes <- ovi defaultOVISettingsDouble uEqMap

  rCertified <- oviToRational defaultOVISettingsDouble uEqMap oviRes
  unless rCertified $ error "cannot deduce a rational certificate for this SCC when computing fraction f"

  unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"

  {-
  DBG.traceM "Approximating via Value Iteration"
  approxVec <- approxFixp eqMap iterEps defaultMaxIters
  approxFracVec <- toRationalProbVec iterEps approxVec

  -- printing stuff - TO BE REMOVED
  forM_  approxFracVec $ \(varKey, _, p) -> do
  liftIO (HT.lookup eqMap varKey) >>= \case
  Just (PopEq _) -> return ()
  Just _ -> DBG.traceM ("Lower bound for " ++ show varKey ++ ": " ++ show p)
  _ -> error "weird error 1"

  nonPops <- filterM (\(varKey, _, _) -> do
  liftIO (HT.lookup eqMap varKey) >>= \case
  Just (PopEq _) -> return False
  Just _ -> return True
  _ -> error "weird error 2"
  ) approxFracVec

  -- TODO: if you restore this code, you will have to handle this by rehaving closing edges on the path
  let actualAsReachesPop = scclen < 2 && asReachesPop

  DBG.traceM "Asserting upper bounds 1 for value iteration"
  forM_ (groupBy (\k1 k2 -> fst k1 == fst k2) . map (\(varKey, _, _) -> varKey) $ nonPops) $ \list -> do
  sumVars <- mkAdd =<< liftIO (mapM (fmap fromJust . HT.lookup newAdded) list)
  assert =<< mkLe sumVars =<< mkRealNum (1 :: EqMapNumbersType)

  -- assert bounds computed by value iteration
  DBG.traceM "Asserting lower and upper bounds computed from value iteration, and getting a model"
  model <- doAssert approxFracVec eps

  -}

  -- updating lower bounds
  approxVec <- approxFixp lEqMap iterEps defaultMaxIters
  forM_  variables $ \varKey -> do
    HT.lookup lEqMap varKey >>= \case
        Just (PopEq _) -> return () -- An eq constraint has already been asserted
        _ -> do
          p <- fromJust <$> HT.lookup approxVec varKey
          addFixpEq lEqMap varKey (PopEq p)

  -- updating upper bounds
  upperBound <- HT.toList (oviUpperBound oviRes)

  let upperBoundsTermProbs = (\mapAll -> Map.restrictKeys mapAll (IntSet.fromList sccMembers)) . Map.fromListWith (+) . map (\(key, ub) -> (fst key, ub)) $ upperBound
  let upperBounds = (\mapAll -> GeneralMap.restrictKeys mapAll (Set.fromList variables)) . GeneralMap.fromList $ upperBound
  --DBG.traceM $ "Computed upper bounds: " ++ show upperBounds
  --DBG.traceM $ "Computed upper bounds on weight w: " ++ show upperBoundsTermProbs

  forM_  variables $ \varKey -> do
    HT.lookup uEqMap varKey >>= \case
      Just (PopEq _) -> return () -- An eq constraint has already been asserted
      _ -> do
        p <- fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
        addFixpEq uEqMap varKey (PopEq p)



