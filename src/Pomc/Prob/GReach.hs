{- |
   Module      : Pomc.GReach
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( Globals
                        , newGlobals
                        , reachableStates 
                        , Delta(..)
                        ) where 

import Pomc.OmegaEncoding (OmegaEncodedSet, OmegaBitencoding)
import qualified Pomc.OmegaEncoding as OE

import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.State(State(..))

import Pomc.SatUtil

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM

import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM

import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef)

import Control.Monad(unless)

import Data.Maybe
import Data.Hashable(Hashable)

import Data.Bifunctor(first)

import qualified Data.HashTable.ST.Basic as BH

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- global variables in the algorithms
data Globals s state = Globals
  { sIdGen :: SIdGen s state
  , visited :: HashTable s (Int,Int,Int) OmegaEncodedSet -- we store the recorded sat set as well
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (MapMap s (StateId state) OmegaEncodedSet) -- we store the formulae satisfied in the support
  , obitenc :: OmegaBitencoding state -- different from the usual bitenc
  , currentInitial :: STRef s Int -- stateId of the current initial state
  }

-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> [state] -- deltaPush relation
  , deltaShift :: state -> [state] -- deltaShift relation
  , deltaPop :: state -> state -> [state] -- deltapop relation
  }

newGlobals :: OmegaBitencoding state -> ST.ST s (Globals s state)
newGlobals obe = do 
  newSig <- initSIdGen
  emptyVisited <- BH.new
  emptySuppStarts <- SM.empty
  emptySuppEnds <- MM.empty
  noInitial <- newSTRef (-1 :: Int)
  return $ Globals { sIdGen = newSig
                   , visited = emptyVisited 
                   , suppStarts = emptySuppStarts 
                   , suppEnds = emptySuppEnds
                   , obitenc = obe
                   , currentInitial = noInitial
                   }

reachableStates :: (SatState state, Eq state, Hashable state, Show state)
   => Globals s state
   -> Delta state -- delta relation of the opa
   -> state -- current state
   -> ST s [(state, OmegaEncodedSet)]
reachableStates globals delta state = do 
  q <- wrapState (sIdGen globals) state
  currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
  if not (null currentSuppEnds)
    then return $ map (first getState) currentSuppEnds
    else do 
      writeSTRef (currentInitial globals) (getId q)
      let newStateSatSet = OE.encodeSatState (obitenc globals) state
      BH.insert (visited globals) (decode (q,Nothing)) newStateSatSet
      reach globals delta (q,Nothing) newStateSatSet
      map (first getState) <$> MM.lookup (suppEnds globals) (getId q)

reach :: (SatState state, Eq state, Hashable state, Show state)
      => Globals s state -- global variables of the algorithm
      -> Delta state -- delta relation of the opa
      -> (StateId state, Stack state) -- current semiconfiguration
      -> OmegaEncodedSet -- current satset
      -> ST s ()
reach globals delta (q,g) pathSatSet = do
  let qState = getState q
      precRel = (prec delta) (fst . fromJust $ g) (current . getSatState $ qState)
      cases i
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && (getId q /= i) = return ()

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
          reachPush globals delta q g qState pathSatSet

        | precRel == Just Equal =
          reachShift globals delta q g qState pathSatSet

        | precRel == Just Take =
          reachPop globals delta q g qState pathSatSet

        | otherwise = return ()
  iniId <- readSTRef (currentInitial globals)
  cases iniId

reachPush :: (SatState state, Eq state, Hashable state, Show state)
  => Globals s state
  -> Delta state
  -> StateId state
  -> Stack state
  -> state
  -> OmegaEncodedSet
  -> ST s ()
reachPush globals delta q g qState pathSatSet = 
  let qProps = getStateProps (bitenc delta) qState
      doPush p = reachTransition globals delta Nothing Nothing (p, Just (qProps, q))
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState
    mapM_ doPush newStates
    currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
    mapM_ (\(s, supportSatSet) -> reachTransition globals delta (Just pathSatSet) (Just supportSatSet) (s,g)) 
      currentSuppEnds

reachShift :: (SatState state, Eq state, Hashable state, Show state)
      => Globals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> state
      -> OmegaEncodedSet
      -> ST s ()
reachShift globals delta _ g qState pathSatSet = 
  let qProps = getStateProps (bitenc delta) qState
      doShift p = reachTransition globals delta (Just pathSatSet) Nothing (p, Just (qProps, snd . fromJust $ g))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState
    mapM_ doShift newStates

reachPop :: (SatState state, Eq state, Hashable state, Show state)
    => Globals s state
    -> Delta state
    -> StateId state
    -> Stack state
    -> state
    -> OmegaEncodedSet
    -> ST s ()
reachPop globals delta _ g qState pathSatSet = 
  let doPop p =
        let r = snd . fromJust $ g
            closeSupports g' = do 
              lcSatSet <- fromJust <$> BH.lookup (visited globals) (decode (r,g'))
              reachTransition globals delta (Just lcSatSet) (Just pathSatSet) (p, g')
        in do
          MM.insertWith (suppEnds globals) (getId r) OE.union p pathSatSet
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ closeSupports currentSuppStarts
  in do 
    newStates <- wrapStates (sIdGen globals) $
      (deltaPop delta) qState (getState . snd . fromJust $ g)
    mapM_  doPop newStates

-- handling the transition to a new semiconfiguration
reachTransition :: (SatState state, Eq state, Hashable state, Show state)
                 => Globals s state
                 -> Delta state
                 -> Maybe OmegaEncodedSet -- the SatSet established on the path so far
                 -> Maybe OmegaEncodedSet -- the SatSet of the edge (Nothing if it is not a Support edge)        
                 -> (StateId state, Stack state) -- to semiconf
                 -> ST s ()
reachTransition globals delta pathSatSet mSuppSatSet dest = 
  let -- computing the new set of sat formulae for the current path in the chain
    newStateSatSet = OE.encodeSatState (obitenc globals) (getState . fst $ dest)
    newPathSatSet = OE.unions (newStateSatSet : catMaybes [pathSatSet, mSuppSatSet])
  in do 
  maybeSatSet <- BH.lookup (visited globals) (decode dest)
  if isNothing maybeSatSet
    then do 
      -- dest semiconf has not been visited so far
      BH.insert (visited globals) (decode dest) newPathSatSet
      reach globals delta dest newPathSatSet
    else do 
      let recordedSatSet = fromJust maybeSatSet
      let augmentedPathSatSet = OE.unions (recordedSatSet : catMaybes [pathSatSet, mSuppSatSet])
      unless (recordedSatSet `OE.subsumes` augmentedPathSatSet) $ do
        -- dest semiconf has been visited, but with a set of sat formulae that does not include the current one
        BH.insert (visited globals) (decode dest) augmentedPathSatSet
        reach globals delta dest augmentedPathSatSet
        