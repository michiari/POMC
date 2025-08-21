{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.SupportGraph
   Copyright   : 2023-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.SupportGraph ( SupportGraph
                              , buildSupportGraph
                              , GraphNode(..)
                              ) where
import Pomc.Prob.ProbUtils
import Pomc.Prec (Prec(..))

import qualified Pomc.CustoMap as CM
import Pomc.SetMap(SetMap)
import qualified Pomc.SetMap as SM

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Set as Set
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Strict.IntMap as IntMap
import Data.Strict.IntMap(IntMap)
import Data.Strict.Map(Map)

import Control.Monad(when)
import Data.Bifunctor (first)
import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, catMaybes, mapMaybe)

import Data.Hashable (Hashable)
import qualified Data.HashTable.ST.Basic as BH
-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- a node in the support graph, corresponding to a semiconfiguration
data GraphNode state = GraphNode
  { gnId   :: Int
  , semiconf   :: (StateId state, Stack state)
  -- if the semiconf is a pop one, these IntMap and IntSet are empty
  , internalEdges :: IntMap Prob
  , supportEdges  :: IntSet
  -- if the semiconf is a pop one, then popContexts represents the probability distribution of the pop transition over "return states", and not semiconfs
  -- otherwise this IntMap is empty
  , popContexts :: IntMap Prob
  } deriving Show

instance Eq (GraphNode state) where
  p == q =  gnId p ==  gnId q

instance  Ord (GraphNode state) where
  compare r q = compare ( gnId r) ( gnId q)

-- the Support Graph computed by this module
type PartialSupportGraph s state = CM.CustoMap s (GraphNode state)
type SupportGraph state = Vector (GraphNode state)
type SidMap state = Map state Int

-- the global variables in the algorithm
data Globals s state = Globals
  { sIdGen     :: SIdGen s state
  , idSeq      :: STRef s Int
  , graphMap   :: HashTable s (Int,Int,Int) Int
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds   :: STRef s (SetMap s (StateId state))
  , graph      :: STRef s (PartialSupportGraph s state)
  }

-- build the support graph of an input pOPA
buildSupportGraph  :: (Ord state, Hashable state, Show state)
        => DeltaWrapper state -- probabilistic delta relation of a popa
        -> (state, Label) -- (initial state of the popa, label of the initial state)
        -> STRef s Stats
        -> ST s (SupportGraph state, SidMap state) -- returning a graph
buildSupportGraph probdelta (i, iLabel) stats = do
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
  CM.insert emptyGraph initialId $ GraphNode {gnId=initialId, semiconf=initialNode, internalEdges= IntMap.empty, supportEdges = IntSet.empty, popContexts = IntMap.empty}
  let globals = Globals { sIdGen = newSig
                        , idSeq = newIdSequence
                        , graphMap = emptyGraphMap
                        , suppStarts = emptySuppStarts
                        , suppEnds = emptySuppEnds
                        , graph = emptyGraph
                        }
  -- compute the support graph of the input popa
  build globals probdelta initialNode
  idx <- readSTRef . idSeq $ globals
  statesCount <- sIdCount newSig
  modifySTRef' stats $ \s -> s{suppGraphLen = idx}
  modifySTRef' stats $ \s -> s{popaStatesCount = statesCount}
  suppGraph <- V.freeze . CM.take idx =<< (readSTRef . graph $ globals)
  sidMap <- sIdMap (sIdGen globals)
  return (suppGraph, sidMap)

build :: (Eq state, Hashable state, Show state)
      => Globals s state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (StateId state, Stack state) -- current semiconfiguration
      -> ST s ()
build globals probdelta (q,g) = do
  let qLabel = getLabel q
      qState = getState q
      precRel = (prec probdelta) (fst . fromJust $ g) qLabel
      cases
        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
          buildPush globals probdelta q g qState qLabel

        | precRel == Just Equal =
          buildShift globals probdelta q g qState qLabel

        | precRel == Just Take =
          buildPop globals probdelta q g qState

        | otherwise = error "unexpected prec rel."
  cases

buildPush :: (Eq state, Hashable state, Show state)
          => Globals s state
          -> DeltaWrapper state
          -> StateId state
          -> Stack state
          -> state
          -> Label
          -> ST s ()
buildPush globals probdelta q g qState qLabel =
  let wrapPush (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        return (prob_, (newState,Just (qLabel, q)))
  in do
    SM.insert (suppStarts globals) (getId q) g
    pushEdges <- mapM wrapPush $ (deltaPush probdelta) qState
    buildInternalTransitions globals probdelta (q,g) pushEdges
    suppEdges <- map (,g) . Set.toList <$> SM.lookup (suppEnds globals) (getId q)
    buildSupportTransitions globals probdelta (q,g) suppEdges

buildShift :: (Eq state, Hashable state, Show state)
           => Globals s state
           -> DeltaWrapper state
           -> StateId state
           -> Stack state
           -> state
           -> Label
           -> ST s ()
buildShift globals probdelta q g qState qLabel =
  let wrapShift (p, pLabel, prob_)= do
        newState <- wrapState (sIdGen globals) p pLabel
        return (prob_, (newState, Just (qLabel, snd . fromJust $ g)))
  in do
    shiftEdges <- mapM wrapShift $ (deltaShift probdelta) qState
    buildInternalTransitions globals probdelta (q,g) shiftEdges

buildPop :: (Eq state, Hashable state, Show state)
         => Globals s state
         -> DeltaWrapper state
         -> StateId state
         -> Stack state
         -> state
         -> ST s ()
buildPop globals probdelta q g qState =
  let r = snd . fromJust $ g
      wrapPop (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        return (newState, prob_)
      doPop (newState, _) =
        let closeSupports g' = buildSupportTransitions globals probdelta (r,g') [(newState, g')]
        in do
          SM.insert (suppEnds globals) (getId r) newState
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ (closeSupports) currentSuppStarts
  in do
    popCntxs <- mapM wrapPop $ (deltaPop probdelta) qState (getState . snd . fromJust $ g)
    addPopContexts globals (q,g) popCntxs
    mapM_ doPop popCntxs

--
-- functions that modify the stored support graph
--

-- add right contexts to a pop semiconfiguration
addPopContexts :: (Eq state, Hashable state, Show state)
                => Globals s state
                -> (StateId state, Stack state) -- from state 
                -> [(StateId state, Prob)]
                -> ST s ()
addPopContexts globals from rCntxs =
  let
    -- we use unionWith (+) and fromListWith (+) because the input distribution might not be normalized - i.e., there might be duplicate pop transitions
    insertContext g@GraphNode{popContexts= cntxs} =g{popContexts = IntMap.unionWith (+) cntxs (IntMap.fromListWith (+) $ map (first getId) rCntxs)}
  in BH.lookup (graphMap globals) (decode from) >>= CM.modify (graph globals) insertContext . fromJust

-- decomposing transitions of a semiconf
buildInternalTransitions :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> DeltaWrapper state
                 -> (StateId state, Stack state) -- from semiconf 
                 -> [(Prob, (StateId state, Stack state))] -- Push/Shift transitions
                 -> ST s ()
buildInternalTransitions globals probdelta from intDests =
  let
    computeId (prob_, dest) = do
      maybeId <- BH.lookup (graphMap globals) (decode dest)
      actualId <- maybe (freshPosId $ idSeq globals) return maybeId
      when (isNothing maybeId) $ do
          BH.insert (graphMap globals) (decode dest) actualId
          CM.insert (graph globals) actualId $ GraphNode {gnId=actualId, semiconf=dest, internalEdges= IntMap.empty, supportEdges = IntSet.empty, popContexts = IntMap.empty}
      return (actualId, prob_, if isNothing maybeId then Just dest else Nothing)
  in do
    intEdges <- mapM computeId intDests
    let -- we use sum here to handle non normalized probability distributions (i.e., multiple probabilities to go to the same state, that have to be summed)
        intEdgs = IntMap.fromListWith (+) . map (\(id_, prob_, _) -> (id_, prob_)) $ intEdges
    fromId <- fromJust <$> BH.lookup (graphMap globals) (decode from)
    CM.modify (graph globals) (\g@GraphNode{internalEdges = intEdges_} -> g{internalEdges = IntMap.unionWith (+) intEdges_ intEdgs}) fromId
    mapM_ (build globals probdelta) $ mapMaybe (\(_,_, maybeDest) -> maybeDest) intEdges

-- decomposing transitions of a semiconf
buildSupportTransitions :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> DeltaWrapper state
                 -> (StateId state, Stack state) -- from semiconf 
                 -> [(StateId state, Stack state)] -- support transitions
                 -> ST s ()
buildSupportTransitions globals probdelta from suppDests =
  let
    computeId dest = do
      maybeId <- BH.lookup (graphMap globals) (decode dest)
      actualId <- maybe (freshPosId $ idSeq globals) return maybeId
      when (isNothing maybeId) $ do
          BH.insert (graphMap globals) (decode dest) actualId
          CM.insert (graph globals) actualId $ GraphNode {gnId=actualId, semiconf=dest, internalEdges= IntMap.empty, supportEdges = IntSet.empty, popContexts = IntMap.empty}
      return (actualId, if isNothing maybeId then Just dest else Nothing)
  in do
    suppEdges <- mapM computeId suppDests
    let suppEds = IntSet.fromList . map fst $ suppEdges
    fromId <- fromJust <$> BH.lookup (graphMap globals) (decode from)
    CM.modify (graph globals) (\g@GraphNode{supportEdges = suppEdges_} -> g{supportEdges = IntSet.union suppEdges_ suppEds}) fromId
    mapM_ (build globals probdelta) $ mapMaybe snd suppEdges
