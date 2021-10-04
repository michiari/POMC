{- |
   Module      : Pomc.SatUtil
   Copyright   : 2021 Michele Chiari and Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SatUtil( SatState(..)
                   , StateId(..)
                   , Stack
                   , SIdGen
                   , initSIdGen
                   , wrapStates
                   , getSidProps
           		     , debug
           		     , freshPosId
           		     , freshNegId 
                   , decode
           		     ) where

import Pomc.State(Input, State(..))
import Pomc.Encoding (BitEncoding, extractInput, nat)

import Data.Maybe
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef') 

import Data.Vector (Vector)
import qualified Data.Vector as V

import Debug.Trace (trace)

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import Control.DeepSeq(NFData(..), deepseq)

--  a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

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
  hashWithSalt _ s = getId s

instance (NFData state) => NFData (StateId state) where 
  rnf (StateId i s) = i `deepseq` s `deepseq` ()

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

-- get atomic propositions holding in a state
getSidProps :: (SatState state) => BitEncoding -> StateId state -> Input
getSidProps bitencoding s = (getStateProps bitencoding) . getState $ s

debug :: String -> a -> a
debug _ x = x
--debug msg r = trace msg r 

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return $ curr

freshNegId :: STRef s Int -> ST.ST s Int
freshNegId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+(-1));
  return $ curr

decode :: (StateId state, Stack state) -> (Int,Int,Int)
decode (s1, Nothing) = (getId s1, 0, 0)
decode (s1, Just (i, s2)) = (getId s1, nat i, getId s2)