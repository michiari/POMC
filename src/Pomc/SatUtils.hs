{- |
   Module      : Pomc.SatUtils
   Copyright   : 2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.SatUtils ( SatState(..)
                     , Delta(..)
                     , StateId(..)
                     , Stack
                     , SIdGen
                     , SetMap
                     , debug
                     , initSIdGen
                     , wrapStates
                     , insertSM
                     , lookupSM
                     , memberSM
                     , emptySM
                     , getSidProps
                     ) where

import Pomc.Check ( EncPrecFunc)
import Pomc.State(Input, State(..))
import Pomc.Data (BitEncoding, extractInput)

import Control.Monad (foldM, forM_)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector)
import qualified Data.Vector as V


--import Debug.Trace (trace)

debug :: String -> ST s a -> ST s a
debug _ x = x
--debug msg r = fmap traceTrue r
--  where traceTrue False = False
--        traceTrue True = trace msg True


-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v



-- Map to sets
type SetMap s v = MV.MVector s (Set v)

-- insert a state into the SetMap
insertSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s ()
insertSM smref stateId val = do
  sm <- readSTRef smref
  let len = MV.length sm
      sid = getId stateId
  if sid < len
    then MV.unsafeModify sm (Set.insert val) sid
    else let newLen = computeLen len sid

             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Set.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Set.insert val) sid
               ; writeSTRef smref grown
               }

lookupSM :: STRef s (SetMap s v) -> StateId state -> ST.ST s (Set v)
lookupSM smref stateId = do
  sm <- readSTRef smref
  let sid = getId stateId
  if sid < MV.length sm
    then MV.unsafeRead sm sid
    else return Set.empty

-- check whether a couple (StateId, Stack) iha already been visited checking the presence of the Stack in the Set at StateId position
memberSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s Bool
memberSM smref stateId val = do
  vset <- lookupSM smref stateId
  return $ val `Set.member` vset

-- an empty Set Map,  an array of sets
emptySM :: ST.ST s (STRef s (SetMap s v))
emptySM = do
  sm <- MV.replicate 4 Set.empty
  newSTRef sm


-- State class for satisfiability
class SatState state where
  getSatState ::  state -> State
  getStateProps :: BitEncoding -> state -> Input

instance SatState State where
  getSatState = id
  {-# INLINABLE getSatState #-}

  getStateProps bitencoding s = extractInput bitencoding (current $ s)
  {-# INLINABLE getStateProps #-}


-- States with unique IDs
data StateId state = StateId { getId :: !Int,
                               getState :: state } deriving (Show)

instance Eq (StateId state) where
  p == q = getId p == getId q

instance Ord (StateId state) where
  compare p q = compare (getId p) (getId q)

instance Hashable (StateId state) where
  hashWithSalt salt s = hashWithSalt salt $ getId s

-- a type to keep track of state to id relation
data SIdGen s state = SIdGen
  { idSequence :: STRef s Int -- a mutable variable in state thread s containing a variable of type Int
  , stateToId :: HashTable s state (StateId state) -- an HashTable where (key,value) = (state, StateId)
  }

initSIdGen :: ST.ST s (SIdGen s state)
initSIdGen = do
  newIdSequence <- newSTRef (1 :: Int) -- build a integer new STRef in the current state thread
  newStateToId <- H.new -- new empty HashTable
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

-- wrap a State into the StateId data type and into the ST monad, and update accordingly SidGen 
wrapState :: (Eq state, Hashable state)
          => SIdGen s state
          -> state
          -> ST.ST s (StateId state)
wrapState sig q = do
  qwrapped <- H.lookup (stateToId sig) q
  if isJust qwrapped
    then return $ fromJust qwrapped
    else do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    let newQwrapped = StateId newId q
    H.insert (stateToId sig) q newQwrapped
    return newQwrapped

--wrap a list of states into the ST monad, giving to each of them a unique ID
wrapStates :: (Eq state, Hashable state)
           => SIdGen s state -- keep track of state to id relation
           -> [state]
           -> ST.ST s (Vector (StateId state))
wrapStates sig states = do
  wrappedList <- V.mapM (wrapState sig) (V.fromList states)
  return wrappedList


-- Stack symbol: (input token, state) || Bottom if empty stack
type Stack state = Maybe (Input, StateId state) 


-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> Input -> [state] -- deltaPush relation
  , deltaShift :: state -> Input -> [state] -- deltaShift relation
  , deltaPop :: state -> state -> [state] -- deltapop relation
  }

-- get atomic propositions holding in a state
getSidProps :: (SatState state) => BitEncoding -> StateId state -> Input
getSidProps bitencoding s = (getStateProps bitencoding) . getState $ s