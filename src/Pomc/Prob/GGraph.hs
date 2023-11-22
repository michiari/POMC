{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GGraph
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GGraph (GGraph
                        , GNode(..)
                        , DeltaWrapper(..)
                        , decomposeGGraph
                        ) where

import Pomc.Prob.ProbUtils hiding (ProbDelta(..))
import Pomc.State(State(..))
import Pomc.SatUtil(SatState(..))
import Pomc.Check (EncPrecFunc)
import Pomc.Prec (Prec(..))


import qualified Pomc.CustoMap as CM

import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.GReach(GRobals)

import Pomc.Prob.SupportGraph(GraphNode(..), Edge(..))

import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE

import qualified Pomc.Encoding as E

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad(when, forM_, foldM)
import Control.Monad.ST (ST)

import Data.STRef (STRef, newSTRef, readSTRef)
import Data.Maybe (fromJust, isNothing)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH

-- A data type for nodes in the augmented graph G
data GNode = GNode
  { gId           :: Int
  , graphNode      :: Int
  , phiNode       :: State
  , edges          :: IntMap ProbEncodedSet -- each (key,value) pair represents an edge. Internal Edges are mapped to empty encoded sets
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

  getStateProps bitEnc (AugState _ p) = getStateProps bitEnc p
  {-# INLINABLE getStateProps #-}

-- the global variables in the algorithm
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (CM.CustoMap s GNode)
  , grGlobals   :: GRobals s (AugState pstate)
  }

-- a type for the probabilistic delta relation of the popa and the delta relation of the phiAutomaton
data DeltaWrapper pState = Delta
  { bitenc :: E.BitEncoding
  , proBitenc :: PE.ProBitencoding
  , prec :: EncPrecFunc
  , deltaPush :: pState -> RichDistr pState Label
  , deltaShift :: pState -> RichDistr pState Label
  , deltaPop :: pState -> pState -> RichDistr pState Label
  , phiDeltaPush :: State -> [State]
  , phiDeltaShift :: State -> [State]
  , phiDeltaPop :: State -> State -> [State]
  }

-- requires: the initial semiconfiguration has id 0
-- pstate: a parametric type for states of the input popa
decomposeGGraph :: (Ord pstate, Hashable pstate, Show pstate)
                => DeltaWrapper pstate
                -> [State] -- initial states of the phiOpa 
                -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                -> (Int -> Bool) -- is a semiconf pending?
                -> ST s (GGraph s)
decomposeGGraph delta phiInitials getGn isPending = do
  -- initialize the global variables
  newIdSequence <- newSTRef (0 :: Int)
  emptyGGraphMap <- BH.new
  emptyGGraph <- CM.empty
  emptyGRGlobals <-  GR.newGRobals
  let newGlobals = GGlobals { idSeq = newIdSequence
                            , ggraphMap = emptyGGraphMap
                            , gGraph = emptyGGraph
                            , grGlobals = emptyGRGlobals
                      }
  iniGn <- getGn 0
  let iniLabel = getLabel . fst . semiconf $ iniGn
  filtered <- foldM (\acc s ->
                      if iniLabel == E.extractInput (bitenc delta) (current s)
                        then do
                          -- create a new GNode 
                        newId <- freshPosId newIdSequence
                        BH.insert emptyGGraphMap (gnId iniGn, s) newId
                        CM.insert emptyGGraph newId $ GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Map.empty}
                        return (s:acc)
                        else return acc
                    )
                []
                phiInitials
  initials <- readSTRef newIdSequence
  forM_ filtered $ \s -> decompose newGlobals delta getGn isPending (iniGn, s)
  g <- readSTRef (gGraph newGlobals)
  return (g, initials)

decompose :: (Ord pstate, Hashable pstate, Show pstate)
          => GGlobals s pstate -- global variables of the algorithm
          -> DeltaWrapper pstate
          -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
          -> (Int -> Bool) -- is a semiconf pending?
          -> (GraphNode pstate, State) -- current GNode
          -> ST s ()
decompose gglobals delta getGn isPending (gn, p) = do
  let
    (q,g) = semiconf gn
    precRel = (prec delta) (fst . fromJust $ g) (getLabel q)
    insertEdge to_  g@GNode{edges = edges_} = g{edges = Map.insertWith PE.union to_ (PE.empty . proBitenc $ delta) edges_}
    cases
      -- semiconfigurations with empty stack but not the initial one
      | (isNothing g) && (getId q /= 0) = do
        gId_ <- fromJust <$> BH.lookup (ggraphMap gglobals) (gnId gn, p) 
        CM.modify (gGraph gglobals) (insertEdge gId_) gId_
  
      -- this case includes the initial push
      | (isNothing g) || precRel == Just Yield =
        decomposePush gglobals delta getGn isPending (gn,p) (isNothing g)

      | precRel == Just Equal =
        decomposeShift gglobals delta getGn isPending (gn, p)

      | precRel == Just Take = error "a pop transition cannot be reached in the augmented graph of pending semiconfs"
      | otherwise = return ()
  cases

decomposeShift :: (Ord pstate, Hashable pstate, Show pstate)
               => GGlobals s pstate -- global variables of the algorithm
               -> DeltaWrapper pstate
               -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
               -> (Int -> Bool) -- is a semiconf pending?
               -> (GraphNode pstate, State) -- current GNopde
               -> ST s ()
decomposeShift gglobals delta getGn isPending (gn, p) =
  let fPendingSemiconfs = Set.toList . Set.filter isPending . Set.map to $(internalEdges gn)
      fPhiStates = (phiDeltaShift delta) p
  in if not . Set.null . supportEdges $ gn
      -- just a sanity check
      then error "a shift semiconf cannot have summaries"
      else do
        fGns <- mapM getGn fPendingSemiconfs
        let fGnodes = [(gn1, p1) | gn1 <- fGns, p1 <- fPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
        forM_ fGnodes $ \(gn1, p1) -> decomposeEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)

decomposePush :: (Ord pstate, Hashable pstate, Show pstate)
              => GGlobals s pstate -- global variables of the algorithm
              -> DeltaWrapper pstate
              -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
              -> (Int -> Bool) -- is a semiconf pending?
              -> (GraphNode pstate, State) -- current gnode
              -> Bool -- is it the initial push?
              -> ST s ()
decomposePush gglobals delta getGn isPending (gn, p) isInitial =
  let fPendingPushSemiconfs = Set.toList . Set.filter isPending . Set.map to $(internalEdges gn)
      fPendingSuppSemiconfs = Set.toList . Set.filter (\i -> isInitial || isPending i) . Set.map to $(supportEdges gn)
      fPushPhiStates = (phiDeltaPush delta) p
  in do 
    -- handling the push edges
    fPushGns <- mapM getGn fPendingPushSemiconfs
    let fPushGnodes = [(gn1, p1) | gn1 <- fPushGns, p1 <- fPushPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
    forM_ fPushGnodes $ \(gn1, p1) -> decomposeEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)
    -- handling the support edges
    fSuppGns <- mapM getGn fPendingSuppSemiconfs
    let leftContext = AugState (getState . fst . semiconf $ gn) p
        cDeltaPush (AugState q p)  =  [(AugState q1 p1 ) | 
                                         (q1, label, _) <- (deltaPush delta) q
                                         , p1 <- (phiDeltaPush delta) p
                                         , label == E.extractInput (bitenc delta) (current p1)
                                      ]
        cDeltaShift (AugState q p) =  [(AugState q1 p1 ) | 
                                         (q1, label, _) <- (deltaShift delta) q
                                         , p1 <- (phiDeltaShift delta) p
                                         , label == E.extractInput (bitenc delta) (current p1)
                                      ]
        cDeltaPop (AugState q p) (AugState q0 p0)  =  [(AugState q1 p1) |
                                                          (q1, label, _) <- (deltaPop delta) q q0
                                                         , p1 <- (phiDeltaPop delta) p p0
                                                         , label == E.extractInput (bitenc delta) (current p1)
                                                      ]
        cDelta = GR.Delta 
                  { GR.bitenc = bitenc delta
                  , GR.proBitenc = proBitenc delta
                  , GR.prec   = prec delta
                  , GR.deltaPush = cDeltaPush
                  , GR.deltaShift = cDeltaShift
                  , GR.deltaPop = cDeltaPop
                  } 
    fSuppAugStates <- GR.reachableStates (grGlobals gglobals) cDelta leftContext
    let fSuppGnodes = [(gn1, p1, suppSatSet) | 
                        gn1 <- fSuppGns
                        , (AugState q p1, suppSatSet) <- fSuppAugStates
                        , (getState . fst . semiconf $ gn1) == q
                      ]
    forM_ fSuppGnodes $ \(gn1, p1, suppSatSet) -> decomposeEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1)

-- decomposing an edge to a new node
decomposeEdge :: (Ord pstate, Hashable pstate, Show pstate)
                 => GGlobals s pstate -- global variables of the algorithm
                 -> DeltaWrapper pstate
                 -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                 -> (Int -> Bool) -- is a semiconf pending?
                 -> (GraphNode pstate, State) -- current node
                 -> ProbEncodedSet -- for formulae satisfied in a support
                 -> (GraphNode pstate, State) -- to node
                 -> ST s ()
decomposeEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1) =
  let
    insertEdge to_  g@GNode{edges = edges_} = g{edges = Map.insertWith PE.union to_ suppSatSet edges_}
    lookupInsert to_ = BH.lookup (ggraphMap gglobals) (gnId gn, p) >>= CM.modify (gGraph gglobals) (insertEdge to_) . fromJust
  in do
    maybeId <- BH.lookup (ggraphMap gglobals) (gnId gn1, p1)
    actualId <- maybe (freshPosId $ idSeq gglobals) return maybeId
    when (isNothing maybeId) $ do
        BH.insert (ggraphMap gglobals) (gnId gn1, p1) actualId
        CM.insert (gGraph gglobals) actualId $ GNode {gId= actualId, graphNode = gnId gn1, phiNode = p1, edges = Map.empty}
    lookupInsert actualId 
    when (isNothing maybeId) $ decompose gglobals delta getGn isPending (gn1, p1)

