{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

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
                           , ProbDelta(..)
                           , SIdGen
                           , Solver(..)
                           , Comp(..)
                           , TermQuery(..)
                           , TermResult(..)
                           , initSIdGen
                           , wrapState
                           , freshPosId
                           , decode
                           , defaultTolerance
                           , isApprox
                           , isCert
                           , toBool
                           , toBoolVec
                           , toProb
                           , toProbVec
                           , debug
                           ) where

import Pomc.State(Input)
import Pomc.Encoding (nat, BitEncoding)
import Pomc.Check (EncPrecFunc)

import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import Data.Vector(Vector)

-- import qualified Debug.Trace as DBG

type Prob = Rational
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

-- a type for the probabilistic delta relation, parametric with respect to the type of the state
data ProbDelta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> RichDistr state Label-- deltaPush relation
  , deltaShift :: state -> RichDistr state Label  -- deltaShift relation
  , deltaPop :: state -> state -> RichDistr state Label -- deltapop relation
  }

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return curr

decode :: (StateId state, Stack state) -> (Int,Int,Int)
decode (s1, Nothing) = (getId s1, 0, 0)
decode (s1, Just (i, s2)) = (getId s1, nat i, getId s2)

-- Strategy to use to compute the result
-- PureSMT: just query the SMT solver
-- SMTWithHints: compute a lower approximation of the solution
--               with an iterative method and use it as a hint for the SMT solver
-- SMTCert: approximate the solution with an iterative method and ask the SMT solver
--          for a certificate within the given tolerance
data Solver = PureSMT | SMTWithHints | SMTCert Double deriving (Eq, Show)

-- Default tolerance to be used with SMTCert
defaultTolerance :: Double
defaultTolerance = 1e-3

-- different termination queries
-- CompQuery asks whether the probability to terminate is <, <=, >, >= than the given probability depending on Comp
-- ApproxQuery requires to approximate the termination probabilities of all semiconfs of the support graph
-- ApproxTermination requires to approximate just the overall termination probability of the given popa
-- Pending requires to compute the ids of pending semiconfs, i.e. those that have a positive probability of non terminating
data TermQuery = CompQuery Comp Prob Solver
               | ApproxAllQuery Solver
               | ApproxSingleQuery Solver
               | PendingQuery Solver
  deriving (Show, Eq)

data Comp = Lt | Le | Gt | Ge deriving (Show, Eq)

-- does the query require to compute some numbers?
isApprox :: TermQuery -> Bool 
isApprox (ApproxAllQuery _) = True
isApprox (ApproxSingleQuery _) = True
isApprox _ = False

isCert :: TermQuery -> Bool
isCert (ApproxAllQuery (SMTCert _)) = True
isCert (ApproxSingleQuery (SMTCert _)) = True
isCert (PendingQuery (SMTCert _)) = True
isCert _ = False

-- different possible results of a termination query
-- ApproxAllResult represents the approximated probabilities to terminate of all the semiconfs of the popa 
-- ApproxSingleResult represents the approximate probability to terminate of the popa 
-- PendingResult represents whether a semiconf is pending (i.e. it has positive probability to non terminate) for all semiconfs of the popa
data TermResult = TermSat | TermUnsat | ApproxAllResult (Vector Prob) | ApproxSingleResult Prob | PendingResult (Vector Bool)
  deriving (Show, Eq, Generic, NFData)

toBool :: TermResult -> Bool 
toBool TermSat = True 
toBool TermUnsat = False 
toBool r = error $ "cannot convert a non boolean result. Got instead: " ++ show r

toProb :: TermResult -> Prob 
toProb (ApproxSingleResult p) = p
toProb r = error $ "cannot convert a non single probability result. Got instead: " ++ show r

toProbVec :: TermResult -> Vector Prob
toProbVec (ApproxAllResult v) = v 
toProbVec r = error $ "cannot convert a non probability vector result. Got instead: " ++ show r

toBoolVec :: TermResult -> Vector Bool
toBoolVec (PendingResult v) = v 
toBoolVec r = error $ "cannot convert a non probability vector result. Got instead: " ++ show r

debug :: String -> a -> a 
--debug = trace
debug _ x = x