{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.SupportGraph
   Copyright   : 2023-2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.SupportGraph ( SupportGraph
                              , GraphNode(..)
                              , TransitionInfo(..)
                              , buildSupportGraph
                              ) where
import Pomc.Prob.ProbUtils
import Pomc.SatUtil(freshPosId)
import Pomc.Prec (Prec(..))

import qualified Pomc.CustoMap as CM
import Pomc.SetMap(SetMap)
import qualified Pomc.SetMap as SM
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Set as Set
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import Data.Strict.Map(Map)
import qualified Data.IntMap as IntMap
import Data.Hashable (Hashable)
import qualified Data.HashTable.ST.Basic as BH

import Control.Monad(when)
import Data.Bifunctor (first)
import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, mapMaybe)

-- information about successor semiconfigurations
data TransitionInfo = Push IntSet (IntMap.IntMap Prob) | Shift (IntMap.IntMap Prob) | Pop (IntMap.IntMap Prob)
  deriving Show

-- a node in the support graph, corresponding to a semiconfiguration
data GraphNode state = GraphNode
  { gnId     :: Int
  , semiconf :: (StateId state, Stack state)
  , gnEdges  :: TransitionInfo
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

lookupId :: (Eq state, Hashable state, Show state)
  => Globals s state
  -> (Prob, (StateId state, Stack state))
  -> ST s (Int, Prob, Maybe (StateId state, Stack state))
lookupId globals (prob_, dest) = do
  maybeId <- BH.lookup (graphMap globals) (decode dest)
  actualId <- maybe (freshPosId $ idSeq globals) return maybeId
  when (isNothing maybeId) $ BH.insert (graphMap globals) (decode dest) actualId
  return (actualId, prob_, if isNothing maybeId then Just dest else Nothing)

lookupIdSupp :: (Eq state, Hashable state, Show state)
  => Globals s state
  -> (StateId state, Stack state)
  -> ST s (Int, Maybe (StateId state, Stack state))
lookupIdSupp globals dest = do
  maybeId <- BH.lookup (graphMap globals) (decode dest)
  actualId <- maybe (freshPosId $ idSeq globals) return maybeId
  when (isNothing maybeId) $ BH.insert (graphMap globals) (decode dest) actualId
  return (actualId, if isNothing maybeId then Just dest else Nothing)

-- build the support graph of an input pOPA
buildSupportGraph  :: (Ord state, Hashable state, Show state)
        => DeltaWrapper state -- probabilistic delta relation of a popa
        -> (state, Label) -- (initial state of the popa, label of the initial state)
        -> STRef s Stats
        -> ST s (SupportGraph state, SidMap state) -- returning a graph
buildSupportGraph probDelta (i, iLabel) stats = do
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
  let globals = Globals { sIdGen = newSig
                        , idSeq = newIdSequence
                        , graphMap = emptyGraphMap
                        , suppStarts = emptySuppStarts
                        , suppEnds = emptySuppEnds
                        , graph = emptyGraph
                        }
  -- compute the support graph of the input popa
  build globals probDelta (initialId, initialNode)
  idx <- readSTRef . idSeq $ globals
  statesCount <- sIdCount newSig
  modifySTRef' stats $ \s -> s{suppGraphLen = idx, popaStatesCount = statesCount}
  suppGraph <- V.freeze . CM.take idx =<< (readSTRef . graph $ globals)
  sidMap <- sIdMap (sIdGen globals)
  return (suppGraph, sidMap)

build :: (Eq state, Hashable state, Show state)
      => Globals s state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (Int, (StateId state, Stack state)) -- current semiconfiguration
      -> ST s ()
build globals probDelta (scId_, (q,g)) =
  let qLabel = getLabel q
      qState = getState q
      precRel = (prec probDelta) (fst . fromJust $ g) qLabel
      cases
        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
          buildPush globals probDelta q g qState qLabel scId_

        | precRel == Just Equal =
          buildShift globals probDelta q g qState qLabel scId_

        | precRel == Just Take =
          buildPop globals probDelta q g qState scId_

        | otherwise = error "unexpected prec rel."
  in cases

buildPush :: (Eq state, Hashable state, Show state)
          => Globals s state
          -> DeltaWrapper state
          -> StateId state
          -> Stack state
          -> state
          -> Label
          -> Int
          -> ST s ()
buildPush globals probDelta q g qState qLabel scId_ =
  let wrapPush (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        return (prob_, (newState,Just (qLabel, q)))
  in do
    SM.insert (suppStarts globals) (getId q) g
    pushEdges <- mapM wrapPush $ (deltaPush probDelta) qState
    suppEdges <- map (,g) . Set.toList <$> SM.lookup (suppEnds globals) (getId q)
    pushSuccs <- mapM (lookupId globals) pushEdges
    suppSuccs <- mapM (lookupIdSupp globals) suppEdges
    let -- we use sum here to handle non normalized probability distributions 
        -- (i.e., multiple probabilities to go to the same state, that have to be summed)
        pushMap = IntMap.fromListWith (+) . map (\(id_, prob_, _) -> (id_, prob_)) $ pushSuccs
        suppSet = IntSet.fromList . map fst $ suppSuccs
        pushInfo = Push suppSet pushMap
    -- adding current Push semiconf to the Support Graph
    CM.insert (graph globals) scId_
      $ GraphNode {gnId=scId_, semiconf=(q,g), gnEdges = pushInfo}
    -- exploring push transitions of the Support Graph
    mapM_ (build globals probDelta) 
      $ mapMaybe (\(id_,_, maybeDest) -> fmap (id_,) maybeDest) pushSuccs
    -- exploring supp transitions of the Support Graph
    mapM_ (build globals probDelta) 
      $ mapMaybe (\(id_,maybeDest) -> fmap (id_,) maybeDest) suppSuccs

buildShift :: (Eq state, Hashable state, Show state)
           => Globals s state
           -> DeltaWrapper state
           -> StateId state
           -> Stack state
           -> state
           -> Label
           -> Int
           -> ST s ()
buildShift globals probDelta q g qState qLabel scId_ =
  let wrapShift (p, pLabel, prob_)= do
        newState <- wrapState (sIdGen globals) p pLabel
        return (prob_, (newState, Just (qLabel, snd . fromJust $ g)))
  in do
    shiftEdges <- mapM wrapShift $ (deltaShift probDelta) qState
    shiftSuccs <- mapM (lookupId globals) shiftEdges
    let -- we use sum here to handle non normalized probability distributions 
        -- (i.e., multiple probabilities to go to the same state, that have to be summed)
        shiftInfo = Shift (IntMap.fromListWith (+) . map (\(id_, prob_, _) -> (id_, prob_)) $ shiftSuccs)
    -- adding current Shift semiconf to the Support Graph
    CM.insert (graph globals) scId_
      $ GraphNode {gnId=scId_, semiconf=(q,g), gnEdges = shiftInfo}
    -- exploring Shift transitions of the Support Graph
    mapM_ (build globals probDelta) $ mapMaybe (\(id_,_, maybeDest) -> fmap (id_,) maybeDest) shiftSuccs

buildPop :: (Eq state, Hashable state, Show state)
         => Globals s state
         -> DeltaWrapper state
         -> StateId state
         -> Stack state
         -> state
         -> Int
         -> ST s ()
buildPop globals probDelta q g qState scId_ =
  let addSupp suppId_ g@GraphNode{gnEdges = Push suppSet pushMap} = 
        g{gnEdges = Push (IntSet.insert suppId_ suppSet) pushMap}
      r = snd . fromJust $ g
      wrapPop (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        return (newState, prob_)
      doPop (newState, _) =
        let closeSupports g' = do 
              fromId <- fromJust <$> BH.lookup (graphMap globals) (decode (r,g'))
              suppSucc <- lookupIdSupp globals (newState, g')
              CM.modify (graph globals) (addSupp (fst suppSucc)) fromId
              case suppSucc of 
                (suppId, Just dest) -> build globals probDelta (suppId, dest)
                _ -> return ()
        in do
          SM.insert (suppEnds globals) (getId r) newState
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ closeSupports currentSuppStarts
  in do
    popCntxs <- mapM wrapPop $ (deltaPop probDelta) qState (getState . snd . fromJust $ g)
    -- adding current Pop semiconf to the Support Graph
    let popInfo = Pop (IntMap.fromListWith (+) $ map (first getId) popCntxs)
    CM.insert (graph globals) scId_
      $ GraphNode {gnId=scId_, semiconf=(q,g), gnEdges = popInfo}
    mapM_ doPop popCntxs