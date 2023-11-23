{- |
   Module      : Pomc.Prob.SupportGraph
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.SupportGraph ( SupportGraph
                              , decomposeGraph
                              , GraphNode(..)
                              , Edge(..)
                              ) where
import Pomc.Prob.ProbUtils
import Pomc.Prec (Prec(..))

import qualified Pomc.CustoMap as CM

import Pomc.SetMap(SetMap)
import qualified Pomc.SetMap as SM

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Control.Monad(when)
import Control.Monad.ST (ST)

import Data.STRef (STRef, newSTRef, readSTRef)
import Data.Maybe (fromJust, isNothing)

import Data.Hashable (Hashable)
import qualified Data.HashTable.ST.Basic as BH
-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

data Edge = Edge
  { to    :: Int
  , prob  :: Prob
  } deriving Show

instance Eq Edge where
  p == q = (to p) == (to q)

instance Ord Edge where
  compare p q = compare (to p) (to q)

-- a node in the support graph, corresponding to a semiconfiguration
data GraphNode state = GraphNode
  { gnId   :: Int
  , semiconf   :: (StateId state, Stack state)
  , internalEdges :: Set Edge
  , supportEdges  :: Set Edge
  -- if the semiconf is a pop one, then popContexts represents the probability distribution of the pop transition 
  , popContexts :: IntMap Prob
  } deriving Show

instance Eq (GraphNode state) where
  p == q =  gnId p ==  gnId q

instance  Ord (GraphNode state) where
  compare r q = compare ( gnId r) ( gnId q)

-- the Support Graph computed by this module
type SupportGraph s state = CM.CustoMap s (GraphNode state)

-- the global variables in the algorithm
data Globals s state = Globals
  { sIdGen     :: SIdGen s state
  , idSeq      :: STRef s Int
  , graphMap   :: HashTable s (Int,Int,Int) Int
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds   :: STRef s (SetMap s (StateId state))
  , graph      :: STRef s (SupportGraph s state)
  }

decomposeGraph  :: (Eq state, Hashable state, Show state)
        => ProbDelta state -- probabilistic delta relation of a popa
        -> state -- initial state of the popa
        -> Label -- label of the initial state
        -> ST s (SupportGraph s state) -- returning a graph
decomposeGraph probdelta i iLabel = do
  -- initialize the global variables
  newSig <- initSIdGen
  emptySuppStarts <- SM.empty
  emptySuppEnds <- SM.empty
  initialsId <- wrapState newSig i iLabel
  let initialNode = (initialsId, Nothing)
  newIdSequence <- newSTRef (0 :: Int)
  emptyGraphMap <- BH.new
  emptyGraph <- CM.empty
  initialId <- freshPosId newIdSequence
  BH.insert emptyGraphMap (decode initialNode) initialId
  CM.insert emptyGraph initialId $ GraphNode {gnId=initialId, semiconf=initialNode, internalEdges= Set.empty, supportEdges = Set.empty, popContexts = Map.empty}
  let globals = Globals { sIdGen = newSig
                        , idSeq = newIdSequence
                        , graphMap = emptyGraphMap
                        , suppStarts = emptySuppStarts
                        , suppEnds = emptySuppEnds
                        , graph = emptyGraph
                        }
  -- compute the support graph of the input popa
  decompose globals probdelta initialNode
  idx <- readSTRef . idSeq $ globals
  fmap (CM.take idx) $ readSTRef . graph $ globals

-- requires: the initial state of the OPA is mapped to StateId with getId 0
decompose :: (Eq state, Hashable state, Show state)
      => Globals s state -- global variables of the algorithm
      -> ProbDelta state -- delta relation of the popa
      -> (StateId state, Stack state) -- current semiconfiguration
      -> ST s ()
decompose globals probdelta (q,g) = do
  let qLabel = getLabel q
      qState = getState q
      precRel = (prec probdelta) (fst . fromJust $ g) qLabel
      cases
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && (getId q /= 0) = return ()

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
          decomposePush globals probdelta q g qState qLabel

        | precRel == Just Equal =
          decomposeShift globals probdelta q g qState qLabel

        | precRel == Just Take =
          decomposePop globals probdelta q g qState

        | otherwise = return ()
  cases

decomposePush :: (Eq state, Hashable state, Show state)
          => Globals s state
          -> ProbDelta state
          -> StateId state
          -> Stack state
          -> state
          -> Label
          -> ST s ()
decomposePush globals probdelta q g qState qLabel =
  let doPush (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        decomposeTransition globals probdelta (q,g) False
          prob_ (newState, Just (qLabel, q))
  in do
    SM.insert (suppStarts globals) (getId q) g
    mapM_ doPush $ (deltaPush probdelta) qState
    currentSuppEnds <- SM.lookup (suppEnds globals) (getId q)
    mapM_ (\s -> decomposeTransition globals probdelta (q,g) True 0 (s,g))  -- summaries are by default assigned probability zero
      currentSuppEnds

decomposeShift :: (Eq state, Hashable state, Show state)
           => Globals s state
           -> ProbDelta state
           -> StateId state
           -> Stack state
           -> state
           -> Label
           -> ST s ()
decomposeShift globals probdelta q g qState qLabel =
  let doShift (p, pLabel, prob_)= do
        newState <- wrapState (sIdGen globals) p pLabel
        decomposeTransition globals probdelta (q,g) False prob_ (newState, Just (qLabel, snd . fromJust $ g))
  in mapM_ doShift $ (deltaShift probdelta) qState

decomposePop :: (Eq state, Hashable state, Show state)
         => Globals s state
         -> ProbDelta state
         -> StateId state
         -> Stack state
         -> state
         -> ST s ()
decomposePop globals probdelta q g qState =
  let doPop (p, pLabel, prob_) =
        let r = snd . fromJust $ g
            closeSupports pwrapped g' = decomposeTransition globals probdelta (r,g') True prob_ (pwrapped, g')
        in do
          newState <- wrapState (sIdGen globals) p pLabel
          addPopContext globals (q,g) prob_ newState
          SM.insert (suppEnds globals) (getId r) newState
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ (closeSupports newState) currentSuppStarts
  in mapM_ doPop $ (deltaPop probdelta) qState (getState . snd . fromJust $ g)

--
-- functions that modify the stored support graph
--

-- add a right context to a pop semiconfiguration
addPopContext :: (Eq state, Hashable state, Show state)
                => Globals s state
                -> (StateId state, Stack state) -- from state 
                -> Prob 
                -> StateId state
                -> ST s ()
addPopContext globals from prob_ rightContext = 
  let 
    -- we use insertWith + because the input distribution might not be normalized - i.e., there might be duplicate pop transitions
    insertContext g@GraphNode{popContexts= cntxs} =g{popContexts = Map.insertWith (+) (getId rightContext) prob_ cntxs}
  in BH.lookup (graphMap globals) (decode from) >>= CM.modify (graph globals) (insertContext) . fromJust

-- decomposing a transition to a new semiconfiguration
decomposeTransition :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> ProbDelta state
                 -> (StateId state, Stack state) -- from semiconf 
                 -> Bool -- is Support
                 -> Prob
                 -> (StateId state, Stack state) -- to semiconf
                 -> ST s ()
decomposeTransition globals probdelta from isSupport prob_ dest =
  let
    -- we use sum here to handle non normalized probability distributions (i.e., multiple probabilities to go to the same state, that have to be summed)
    createInternal to_  stored_edges = Edge{to = to_, prob = sum $ prob_ : (Set.toList . Set.map prob . Set.filter (\e -> to e == to_) $ stored_edges)}
    insertEdge to_  True  g@GraphNode{supportEdges = edges_} = g{supportEdges = Set.insert Edge{to = to_, prob = 0} edges_} -- summaries are assigned prob 0 by default
    insertEdge to_  False g@GraphNode{internalEdges = edges_} = g{internalEdges = Set.insert (createInternal to_ edges_) edges_  }
    lookupInsert to_ = BH.lookup (graphMap globals) (decode from) >>= CM.modify (graph globals) (insertEdge to_ isSupport) . fromJust
  in do
    maybeId <- BH.lookup (graphMap globals) (decode dest)
    actualId <- maybe (freshPosId $ idSeq globals) return maybeId
    when (isNothing maybeId) $ do
        BH.insert (graphMap globals) (decode dest) actualId
        CM.insert (graph globals) actualId $ GraphNode {gnId=actualId, semiconf=dest, internalEdges= Set.empty, supportEdges = Set.empty, popContexts = Map.empty}
    lookupInsert actualId 
    when (isNothing maybeId) $ decompose globals probdelta dest
