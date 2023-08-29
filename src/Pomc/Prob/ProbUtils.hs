{- |
   Module      : Pomc.Prob.ProbUtils.hs
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbUtils ( Prob 
                        , Distr(..)
                        , RichDistr
                        , Label
                        , StateId(..)
                        , Stack
                        , SIdGen
                        , initSIdGen
                        , wrapState
                        , freshPosId
                        , decode
                        ) where

import Pomc.State(Input)
import Pomc.Encoding(nat)

import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

type Prob = Double
newtype Distr a = Distr [(a, Prob)] deriving Show
-- a distribution over elements of type a 
-- with some additional labels of type b
type RichDistr a b = [(a, b, Prob)]

-- in probabilistic systems the input is replaced by state labels
type Label = Input

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- States with unique IDs
data StateId state = StateId { getId :: !Int
                             , getState :: state
                             , getLabel :: Label 
                             } deriving (Show)

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
  newIdSequence <- newSTRef (0 :: Int) -- build a integer new STRef in the current state thread
  newStateToId <- H.new -- new empty HashTable
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

-- wrap a State into the StateId data type and into the ST monad, and update accordingly SidGen
wrapState :: (Eq state, Hashable state)
          => SIdGen s state
          -> state
          -> Label
          -> ST.ST s (StateId state)
wrapState sig q l = do
  qwrapped <- H.lookup (stateToId sig) q
  maybe (do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    let newQwrapped = StateId newId q l
    H.insert (stateToId sig) q newQwrapped
    return newQwrapped) return qwrapped

-- Stack symbol: (input token, state) || Bottom if empty stack
type Stack state = Maybe (Input, StateId state)

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return curr

decode :: (StateId state, Stack state) -> (Int,Int,Int)
decode (s1, Nothing) = (getId s1, 0, 0)
decode (s1, Just (i, s2)) = (getId s1, nat i, getId s2)

