{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GUtil
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GUtil ( GNode(..)
                        , AugState(..)
                        , GGraph 
                        , HEdge(..)
                        , GGlobals(..)
                        , HashTable
                        , GraphNodesSCC
                        ) where
import Pomc.SatUtil(SatState(..))
import Pomc.State(State(..))
import Pomc.GStack(GStack)
import Pomc.Prob.ProbUtils hiding (sIdMap, SIdGen)
import qualified Pomc.CustoMap as CM
import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import  Data.Strict.IntMap(IntMap)
import Data.Set(Set)
import Data.IntSet(IntSet)
import Data.STRef (STRef)
import GHC.Generics (Generic)
import Data.Hashable

-- A data type for nodes in the augmented graph G
data GNode = GNode
  { gId        :: Int
  , graphNode  :: Int
  , phiNode    :: State
  , edges      :: Set HEdge
  -- -- needed for the SCC algorithm
  , iValue     :: Int
  , descSccs   :: IntSet
  } deriving Show

instance Eq GNode where
  p == q =  gId p ==  gId q

instance  Ord GNode where
  compare p q = compare ( gId p) ( gId q)

instance Hashable GNode where
  hashWithSalt salt s = hashWithSalt salt $ gId s

-- a state in the cross product between the popa and the phiAutomaton
-- similar to MCState in the non probabilistic case
data AugState pstate =  AugState (StateId pstate) State deriving (Generic, Eq, Show, Ord)

instance Hashable (AugState state) where
  hashWithSalt salt (AugState sId phiState) = hashWithSalt salt $ pack phiState
    where
      pack WState{current = curr, pending = pend, stack = st, 
              mustPush = mP, mustShift = mS, afterPop = aP} = 
        (getId sId, curr, pend, st, mP, mS, aP)
      pack _ = error "state for finite-string model checking"

instance SatState (AugState s) where
  getSatState (AugState _ p) = p
  {-# INLINABLE getSatState #-}

  -- always promote the label
  getStateProps _ (AugState sId _ ) = getLabel sId
  {-# INLINABLE getStateProps #-}

-- a type for Graph G
type GGraph s = CM.CustoMap s GNode
type GraphNodesSCC = IntSet

data HEdge = Internal {probInt :: Prob, toG :: Int} |
  Support {toG :: Int, satSet :: ProbEncodedSet} |
  SupportAndInternal {probInt :: Prob, toG :: Int, satSet :: ProbEncodedSet}
  deriving Show

instance Eq HEdge where
  p == q = (toG p) == (toG q)

instance Ord HEdge where
  compare p q = compare (toG p) (toG q)

-- the global variables in the algorithm for constructing and analysing graph G
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (GGraph s)
  , grGlobals   :: GR.GReachGlobals s (AugState pstate)
  , sStack     :: GStack s HEdge
  , bStack     :: GStack s Int
  , cGabow     :: STRef s Int
  -- bottom SCCs of subgraph H
  -- in qualitative model checking, we store only those reachable 
  -- from an initial state where input formula phi does not hold
  , bottomHSCCs  :: STRef s (IntMap GraphNodesSCC)
  }
