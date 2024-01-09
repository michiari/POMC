{- |
   Module      : Pomc.GReach
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( GRobals(..)
                        , newGRobals
                        , reachableStates
                        , showGrobals
                        , Delta(..)
                        ) where
import Pomc.Prob.ProbUtils(Prob, EqMapNumbersType)
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
import qualified Pomc.Prob.ProbEncoding as PE

import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)

import Pomc.SatUtil

import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

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

import Data.Vector(Vector)
import qualified Data.Vector as V

import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad.ST (ST, RealWorld)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef)

import Control.Monad(unless, when)

import Data.Maybe
import Data.Hashable(Hashable)

import Data.Bifunctor(first)

import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as BC
import qualified Data.HashTable.IO as HT

import qualified Data.Vector.Mutable as MV
import Control.Monad (foldM)
import GHC.IO (stToIO)

import Data.IORef (IORef, newIORef, modifyIORef, readIORef, writeIORef, modifyIORef')

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
type SuccessorsPopContexts = IntSet

data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , varMap     :: IORef (IOSetMap Int) -- variables associated with a semiconf
  , sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , successorsCntxs :: MV.IOVector SuccessorsPopContexts
  , cannotReachPop :: IORef IntSet
  , eqMap :: EqMap EqMapNumbersType
  }



lookupSemiconf :: WeightedGRobals state -> (Int, Int, Int) -> Int ->  IO ((Int,Int), Bool)
lookupSemiconf globals decoded rightContext = do
  maybeId <- HT.lookup (graphMap globals) decoded
  when (isNothing maybeId) $ error "future semiconfs should have been already visited"
  let id_ = fromJust maybeId
      key = (id_, rightContext)
      (_, a,b) = decoded
  when ((a,b) == (0,0) || rightContext == -1) $ error "this should not happen"
  asPendingIdxes <- readIORef (cannotReachPop globals)
  if IntSet.member id_ asPendingIdxes
      then addFixpEq (eqMap globals) key (PopEq 0) >> return (key, True)
        else do
            previouslyVisited <- IOSM.member (varMap globals) id_ rightContext
            if previouslyVisited
              then return (key, True)
              else IOSM.insert (varMap globals) id_ rightContext >> return (key, False)


encode :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> (StateId state, Stack state)
  -> Int
  -> IO ()
encode globals sIdGen delta supports (q,g) rightContext = do 
  semiconfId <- fromJust <$> HT.lookup (graphMap globals) (decode (q,g))
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases

        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Equal =
            encodeShift globals sIdGen delta supports q g qState (semiconfId, rightContext)

        | precRel == Just Take = do
            --when (rightContext < 0) $ error $ "Reached a pop with unconsistent left context: "
            popDistribution <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (getId p,prob_)) $ (deltaPush delta) qState
            let e = Map.findWithDefault 0 rightContext $ Map.fromList popDistribution
            addFixpEq (eqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational e

        | otherwise = fail "unexpected prec rel"
  cases

encodePush :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodePush globals sIdGen delta supports q g qState (semiconfId, rightContext) =
  let suppEnds = supports V.! getId q
      qProps = getStateProps (bitenc delta) qState
      recurse (dest, rc) = encode globals sIdGen delta supports dest rc
      closeSupports pushDest (unencodedSCs, terms) suppId =
        let suppDest = (suppId, g) in do
        vars <- mapM (uncurry (lookupSemiconf globals)) [(decode pushDest, getId suppId), (decode suppDest, rightContext)]
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
    addFixpEq (eqMap globals) (semiconfId, rightContext) $ PushEq $ concat terms
    mapM_ recurse unencodedSCs

encodeInitialPush :: (SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> Vector (Set(StateId state))
    -> StateId state
    -> Stack state
    -> state
    -> Int
    -> Int
    -> IO ()
encodeInitialPush globals sIdGen delta supports q _ qState semiconfId suppId =
    let qProps = getStateProps (bitenc delta) qState
        recurse dest = encode globals sIdGen delta supports dest suppId
        pushEnc (newSCs, terms) (p, prob_) =
          let dest = (p, Just (qProps, q)) in do
            (key, alreadyEncoded) <- lookupSemiconf globals (decode dest) suppId
            return ( if alreadyEncoded then newSCs else dest:newSCs
                  , (prob_, key, (suppId, -1)):terms
                  )
  
    in do
      newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
      (unencodedSCs, terms) <- foldM pushEnc ([], []) newStates
      addFixpEq (eqMap globals) (semiconfId, -1) $ PushEq terms
      addFixpEq (eqMap globals) (suppId, -1) $ PopEq (1 :: Double)
      mapM_ recurse unencodedSCs

encodeShift :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IO ()
encodeShift globals sIdGen delta supports q g qState (semiconfId, rightContext) =
  let qProps = getStateProps (bitenc delta) qState
      recurse dest = encode globals sIdGen delta supports dest rightContext
      shiftEnc (newSCs, terms) (p, prob_) = do
        let dest = (p, Just (qProps, snd . fromJust $ g))
        (key, alreadyEncoded) <- lookupSemiconf globals (decode dest) rightContext
        return ( if alreadyEncoded then newSCs else dest:newSCs
                , (prob_, key):terms
                )
  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaShift delta) qState
    (unencodedSCs, terms) <- foldM shiftEnc ([], []) newStates
    addFixpEq (eqMap globals) (semiconfId, rightContext) $ ShiftEq terms
    mapM_ recurse unencodedSCs




