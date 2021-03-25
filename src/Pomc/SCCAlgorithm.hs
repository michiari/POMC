{- |
   Module      : Pomc.SCC
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm () where
 -- TODO. optimize imports
import Pomc.Satisfiability( StateId(..), Stack) 
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.PotlV2(Formula)
import Pomc.PropConv (APType) 
import Pomc.Data (FormulaSet, BitEncoding(..)) 
import qualified Data.Stack.ST  as StackST 

import Control.Monad (foldM, forM_, forM) 
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef') 
import Data.Maybe 

import Data.Set (Set) 
import qualified Data.Set as Set 

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import GHC.Natural(naturalToInt)


import qualified Data.Vector.Mutable as MV 
import Data.Vector (Vector) 
import qualified Data.Vector as V 
import Data.List


------------------------------------ OMEGA CASE ------------------------------------------------------------------
data Edge k = Internal 
  { from :: k
  ,  to  :: k 
  } | Summary 
  { from :: k
  ,   to :: k
  ,  body :: Set (Edge k) 
  } deriving (Show, Ord)-- is it fine to derive Ord?

instance (Eq k, Ord k) => Eq (Edge k) where
  p@(Internal{}) == q@(Internal{}) = (from p) == (from q) && (to p) == (to q) 
  p@(Summary{})  == q@(Summary{}) = (from p) ==( from q) 
                                    && (to p) == (to q )
                                    && (all (\e -> Set.member e (body q)) $ Set.toList (body p))
                                    && (all (\e -> Set.member e (body p)) $ Set.toList (body q))
  _ == _ = False

  -- TODO: devo rendere Edge instance of Ord as well??


-- the nodes which form a  summary body
data SummaryBody k = SummaryBody 
  { firstNode :: k
  , lastNode  :: k 
  , bodyEdges :: Set (Edge k)
  }

data GraphNode k state = SCComponent
  { getgnId   :: k -- immutable
  , iValue    :: Int -- changes at each iteration of the Gabow algorithm
  , nodes     :: Set (GraphNode k state)
  } | SingleNode
  { getgnId  :: k -- immutable
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
  } deriving (Show)

instance (Eq k) => Eq (GraphNode k state) where
  p == q = getgnId p == getgnId q

instance (Ord k) => Ord (GraphNode k state) where
  compare p q = compare (getgnId p) (getgnId q)

instance (Hashable k) => Hashable (GraphNode k state) where
  hashWithSalt salt s = hashWithSalt salt $ getgnId s

type HashTable s k v = BH.HashTable s k v
type DoubleHashTable s k v = (HashTable s k Int, HashTable s Int v)
type TwinSet a = (Set a, Set a)
type Key state = (StateId state, Stack state)
type Value k state = GraphNode k state
type GabowStack s v = StackST.Stack s v

-- this is not parametrized
data Graph s state = Graph
  { idSeq           :: STRef s Int
  , nodeToGraphNode :: DoubleHashTable s (Key state) (Value Int state)
  , edges           :: STRef s (Set (Edge Int)) -- Set is not keyed in the monad, it needs a STRef
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GabowStack s Int -- for the Gabow algorithm
  , sStack          :: GabowStack s Int -- for the Gabow algorithm
  , initials        :: STRef s (TwinSet Int)
  , summaries       :: STRef s (Set (Int -> Edge Int, Key state))
  } 

