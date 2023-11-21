{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GGraph
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GGraph (GGraph
                        , decomposeGGraph
                        , qualitativeModelChecking
                        , GNode(..)

                        ) where

import Pomc.Prob.ProbUtils
import Pomc.State(State(..))
import Pomc.SatUtil(SatState(..))

import qualified Pomc.CustoMap as CM

import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.GReach(GRobals, Delta(..))

import Pomc.Prob.SupportGraph(GraphNode(..))

import Pomc.Prob.ProbEncoding(ProBitencoding, ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE

import Pomc.SetMap(SetMap)
import qualified Pomc.SetMap as SM

import qualified Pomc.Encoding as E

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import Control.Monad(when, forM_, foldM)
import Control.Monad.ST (ST)

import Data.STRef (STRef, newSTRef, readSTRef)
import Data.Maybe (fromJust, isNothing)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH

data Edge = Internal {to :: Int} |
    Support {to :: Int, supportSatSet :: ProbEncodedSet }
    deriving Show

instance Eq Edge where
    p == q = (to p) == (to q)

instance Ord Edge where
    compare p q = compare (to p) (to q)

-- A data type for nodes in the augmented graph G
data GNode = GNode
  { gId           :: Int
  , graphNode      :: Int
  , phiNode       :: State
  , edges          :: IntMap ProbEncodedSet -- each (key,value) pair represents an edge. Internal Edges are mapped to empty encoded sets
  , recordedPhiStates :: [State] -- the stack phi states are not unique per each GNode
  } deriving Show

instance Eq GNode where
  p == q =  gId p ==  gId q

instance  Ord GNode where
  compare p q = compare ( gId p) ( gId q)

instance Hashable GNode where
  hashWithSalt salt s = hashWithSalt salt $ gId s

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- the G Graph computed by this module
type GGraph s = (CM.CustoMap s GNode, Int)

-- a state in the cross product between the popa and the phiAutomaton
-- similar to MCState in the non probabilistic case
data AugState pstate =  AugState pstate State deriving (Generic, Eq, Show, Ord)

instance Hashable s => Hashable (AugState s)

instance SatState (AugState s) where
  getSatState (AugState _ p) = p
  {-# INLINABLE getSatState #-}

  getStateProps bitenc (AugState _ p) = getStateProps bitenc p
  {-# INLINABLE getStateProps #-}

-- the global variables in the algorithm
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (CM.CustoMap s GNode)
  , grGlobals   :: GRobals s (AugState pstate)
  }

-- requires: the initial semiconfiguration has id 0
-- pstate: a parametric type for states of the input popa
decomposeGGraph :: (Ord pstate, Hashable pstate, Show pstate)
                => ProBitencoding
                -> ProbDelta pstate -- probabilistic delta relation of a popa
                -> Delta State -- (revisited) delta relation of the phiOpa
                -> [State] -- initial states of the phiOpa 
                -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                -> (Int -> Bool) -- is a semiconf pending?
                -> ST s (GGraph s)
decomposeGGraph proBitenc probDelta phiDelta phiInitials getGn isPending = do
  -- initialize the global variables
  newIdSequence <- newSTRef (0 :: Int)
  emptyGGraphMap <- BH.new
  emptyGGraph <- CM.empty
  emptyGRGlobals <-  GR.newGRobals proBitenc
  let newGlobals = GGlobals { idSeq = newIdSequence
                            , ggraphMap = emptyGGraphMap
                            , gGraph = emptyGGraph
                            , grGlobals = emptyGRGlobals
                      }
  iniGn <- getGn 0
  let iniLabel = getLabel . fst . semiconf $ iniGn
  filtered <- foldM (\acc s ->
                      if iniLabel == E.extractInput (phiBitenc phiDelta) (current s)
                        then do
                          -- create a new GNode 
                        newId <- freshPosId newIdSequence
                        BH.insert emptyGGraphMap (gnId iniGn, s) newId
                        CM.insert emptyGGraph newId $ GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Map.empty, recordedPhiStates = []}
                        return (s:acc)
                        else return acc
                    )
                []
                phiInitials
  initials <- readSTRef newIdSequence
  forM_ filtered $ decompose newGlobals probDelta phiDelta getGn isPending iniGn
  g <- readSTRef (gGraph newGlobals)
  return (g, initials)

decompose :: (Ord pstate, Hashable pstate, Show pstate)
          => GGlobals s pstate -- global variables of the algorithm
          -> ProbDelta pstate -- delta relation of the popa
          -> Delta State -- (revisited) delta relation of the phiOpa
          -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
          -> (Int -> Bool) -- is a semiconf pending?
          -> GraphNode pstate -- current semiconfiguration
          -> State -- current opba state
          -> ST s ()
decompose gglobals probdelta phiDelta getGn isPending gn s = error "not implemented yet"


qualitativeModelChecking :: ST s Bool
qualitativeModelChecking = error "not implementedy yet"
