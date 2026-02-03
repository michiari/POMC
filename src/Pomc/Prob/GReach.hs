{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.GReach
   Copyright   : 2023-2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( GReachGlobals(..)
                        , Delta(..)
                        , newGReachGlobals
                        , nrSemiconfs
                        , reachableStates
                        , showGReachGlobals
                        , freezeSuppEnds
                        , freezeSuppStarts
                        ) where
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
import qualified Pomc.Prob.ProbEncoding as PE
import Pomc.Prob.ProbUtils(HashTable)

import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.SatUtil

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM
import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM
import qualified Data.Map as Map

import Data.Vector(Vector)
import qualified Data.Vector as V

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
import GHC.IO (stToIO)

-- global variables for detecting reachable right contexts of suppEnds edges in graph G
data GReachGlobals s state = GReachGlobals
  { sIdGen :: SIdGen s state
  , visited :: HashTable s (Int,Int,Int) ProbEncodedSet -- we store the recorded sat set as well
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (MapMap s (StateId state) ProbEncodedSet) -- we store the formulae satisfied in the support
  , currentInitial :: STRef s Int -- stateId of the current initial state
  }

showGReachGlobals :: (Show state) => GReachGlobals s state -> ST s String
showGReachGlobals globals = do
  s1 <- SM.showSetMap =<< readSTRef (suppStarts globals)
  s2 <- MM.showMapMap =<< readSTRef (suppEnds globals)
  s3 <- concatMap show <$> BC.toList (visited globals)
  return $ "SuppStarts: " ++ s1 ++ "---- SuppEnds: " ++ s2 ++ "---- Visited: " ++ s3

-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , proBitenc :: ProBitencoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> [state] -- deltaPush relation
  , deltaShift :: state -> [state] -- deltaShift relation
  , deltaPop :: state -> state -> [state] -- deltapop relation
  , consistentFilter :: state -> Bool
  }

newGReachGlobals :: ST.ST s (GReachGlobals s state)
newGReachGlobals = do
  newSig <- initSIdGen
  emptyVisited <- BH.new
  emptySuppStarts <- SM.empty
  emptySuppEnds <- MM.empty
  noInitial <- newSTRef (-1 :: Int)
  return $ GReachGlobals { sIdGen = newSig
                   , visited = emptyVisited
                   , suppStarts = emptySuppStarts
                   , suppEnds = emptySuppEnds
                   , currentInitial = noInitial
                   }

nrSemiconfs :: GReachGlobals s state -> ST.ST s Int
nrSemiconfs globals = BH.size (visited globals)

freezeSuppEnds :: GReachGlobals RealWorld state -> IO (Vector (Vector (StateId state)))
freezeSuppEnds globals = stToIO $ do
  computedSuppEnds <- readSTRef (suppEnds globals)
  V.map (V.fromList . Map.keys) <$> V.freeze computedSuppEnds

freezeSuppStarts :: GReachGlobals RealWorld state -> IO (Vector [Stack state])
freezeSuppStarts globals = stToIO $ do
  computedSuppStarts <- readSTRef (suppStarts globals)
  V.map Set.toList <$> V.freeze computedSuppStarts

reachableStates :: (SatState state, Eq state, Hashable state, Show state)
  => GReachGlobals s state
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
  => GReachGlobals s state -- global variables of the algorithm
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
  => GReachGlobals s state
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
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState
    mapM_ doPush newStates
    currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
    mapM_ (\(s, supportSatSet) -> reachTransition globals delta (Just pathSatSet) (Just supportSatSet) (s,g))
      $ filter (isConsistentOrPop . fst) currentSuppEnds

reachShift :: (SatState state, Eq state, Hashable state, Show state)
      => GReachGlobals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> state
      -> ProbEncodedSet
      -> ST s ()
reachShift globals delta _ g qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doShift p = reachTransition globals delta (Just pathSatSet) Nothing (p, Just (qProps, snd . fromJust $ g))
  in wrapStates (sIdGen globals) ((deltaShift delta) qState) >>= mapM_ doShift

reachPop :: (SatState state, Eq state, Hashable state, Show state)
    => GReachGlobals s state
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
  in wrapStates (sIdGen globals) ((deltaPop delta) qState gState) >>= mapM_ doPop

-- handling the transition to a new semiconfiguration
reachTransition :: (SatState state, Eq state, Hashable state, Show state)
                 => GReachGlobals s state
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