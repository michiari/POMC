{- |
   Module      : Pomc.Prob.SummaryChain
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.SummaryChain ( ProbDelta(..)
                              , SummaryChain
                              , decomposeGraph
                              , GraphNode(..)
                              , InternalEdge(..)
                              , SummaryEdge(..)
                              ) where

import Pomc.Prob.ProbUtils

import Pomc.Check (EncPrecFunc)
import Pomc.Encoding (BitEncoding)

-- check imports from here


import Pomc.Prec (Prec(..),)
import Pomc.SetMap
import qualified Pomc.SetMap as SM

import Control.Monad (when)
import Control.Monad.ST (ST)

import Data.STRef (STRef, newSTRef, readSTRef)
import Data.Maybe

import qualified Pomc.MaybeMap as MM

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH

data InternalEdge = Internal
  { toI    :: Int
  , probI  :: Prob
  } deriving Show
  
data SummaryEdge = Summary 
  { toS  :: Int
  , probS   :: Prob
  } deriving Show

-- a node in the graph of semiconfigurations
data GraphNode state = GraphNode
  { gnId   :: Int
  , node   :: (StateId state, Stack state)
  , internalEdges  :: [InternalEdge]
  , summaryEdges :: [SummaryEdge]
  }

instance Show (GraphNode state) where
  show gn =  show $ gnId gn

instance Eq (GraphNode state) where
  p == q =  gnId p ==  gnId q

instance  Ord (GraphNode state) where
  compare r q = compare ( gnId r) ( gnId q)

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- the Summary Chain computed by this module
type Chain s state = MM.MaybeMap s (GraphNode state)

-- the global variables in the algorithm
data Globals s state = Globals
  { sIdGen     :: SIdGen s state
  , idSeq      :: STRef s Int
  , chainMap   :: HashTable s (Int,Int,Int) Int
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds   :: STRef s (SetMap s (StateId state))
  , chain      :: STRef s (Chain s state)
  }

-- a type for the output of the decomposition algorithm
type SummaryChain s state = (SetMap s (Stack state), SetMap s (StateId state), Chain s state)

-- a type for the probabilistic delta relation, parametric with respect to the type of the state
data ProbDelta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> RichDistr state Label-- deltaPush relation
  , deltaShift :: state -> RichDistr state Label  -- deltaShift relation
  , deltaPop :: state -> state -> RichDistr state Label -- deltapop relation
  }

decomposeGraph  :: (Eq state, Hashable state, Show state)
        => ProbDelta state -- probabilistic delta relation of a popa
        -> state -- initial state of the popa
        -> Label -- label of the initial state
        -> ST s (SummaryChain s state) -- returning a chain
decomposeGraph probdelta i iLabel = do
  -- initialize the global variables
  newSig <- initSIdGen
  emptySuppStarts <- SM.empty
  emptySuppEnds <- SM.empty
  initialsId <- wrapState newSig i iLabel
  let initialNode = (initialsId, Nothing)
  newIdSequence <- newSTRef (0 :: Int)
  emptyChainMap <- BH.new
  emptyChain <- MM.empty
  initialId <- freshPosId newIdSequence
  BH.insert emptyChainMap (decode initialNode) initialId
  MM.insert emptyChain initialId $ GraphNode {gnId=initialId, node=initialNode, internalEdges= [], summaryEdges = []}
  let globals = Globals { sIdGen = newSig
                        , idSeq = newIdSequence
                        , chainMap = emptyChainMap
                        , suppStarts = emptySuppStarts
                        , suppEnds = emptySuppEnds
                        , chain = emptyChain
                        }
  -- compute the summary chain of the input popa
  decompose globals probdelta initialNode
  ss <- readSTRef . suppStarts $ globals
  se <- readSTRef . suppEnds $ globals
  c <- readSTRef . chain $ globals
  return (ss, se, c)

decompose :: (Eq state, Hashable state, Show state)
      => Globals s state -- global variables of the algorithm
      -> ProbDelta state -- delta relation of the opa
      -> (StateId state, Stack state) -- current semiconfiguration
      -> ST s ()
decompose globals probdelta (q,g) = do
  let qLabel = getLabel q
      qState = getState q
      precRel = (prec probdelta) (fst . fromJust $ g) qLabel
      cases
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
  let doPush (p, pLabel, prob) = do
        newState <- wrapState (sIdGen globals) p pLabel
        SM.insert (suppStarts globals) (getId q) g
        exploreTransition globals probdelta (q,g)
          prob (newState, Just (qLabel, q))  False
  in do
    mapM_ doPush $ (deltaPush probdelta) qState
    currentSuppEnds <- SM.lookup (suppEnds globals) (getId q)
    mapM_ (\s -> do
                exploreTransition globals probdelta (q,g) 0 (s,g) True
          )
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
  let doShift (p, pLabel, prob)= do
        newState <- wrapState (sIdGen globals) p pLabel
        exploreTransition globals probdelta (q,g) prob (newState, Just (qLabel, snd . fromJust $ g)) False
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
            closeSupports pwrapped g' = do
              addEdge globals probdelta (r,g') 0 (pwrapped ,g') True
              exploreTransition globals probdelta (q,g) prob_ (pwrapped ,g') False
        in do
          newState <- wrapState (sIdGen globals) p pLabel
          SM.insert (suppEnds globals) (getId r) newState
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ (closeSupports newState) currentSuppStarts
  in mapM_ doPop $ (deltaPop probdelta) qState (getState . snd . fromJust $ g)

addEdge :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> ProbDelta state
                 -> (StateId state, Stack state)
                 -> Prob
                 -> (StateId state, Stack state)
                 -> Bool
                 -> ST s ()
addEdge = decomposeTransition False

exploreTransition :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> ProbDelta state
                 -> (StateId state, Stack state)
                 -> Prob
                 -> (StateId state, Stack state)
                 -> Bool
                 -> ST s ()
exploreTransition = decomposeTransition True

decomposeTransition :: (Eq state, Hashable state, Show state)
                 => Bool
                 -> Globals s state
                 -> ProbDelta state
                 -> (StateId state, Stack state)
                 -> Prob
                 -> (StateId state, Stack state)
                 -> Bool
                 -> ST s ()
decomposeTransition recurse globals probdelta from prob_ dest isSummary =
  let
    createSummary to_  = Summary{toS = to_, probS = prob_}
    createInternal to_ = Internal{toI = to_, probI = prob_}
    insertEdge to_  True  g@GraphNode{summaryEdges = edges_} = g{summaryEdges = (createSummary to_ ) : edges_}
    insertEdge to_  False g@GraphNode{internalEdges = edges_} = g{internalEdges = (createInternal to_ ) : edges_}
  in do
  maybeid <- BH.lookup (chainMap globals) (decode dest)
  fromid <- BH.lookup (chainMap globals) (decode from) >>= return . fromJust
  if isJust maybeid
    then do
      MM.modify (chain globals) fromid $ insertEdge (fromJust maybeid) isSummary
    else do
      newIdent <- freshPosId $ idSeq globals
      BH.insert (chainMap globals) (decode dest) newIdent
      MM.insert (chain globals) newIdent $ GraphNode {gnId=newIdent, node=dest, internalEdges= [], summaryEdges = []}
      MM.modify (chain globals) fromid $ insertEdge newIdent isSummary
      when recurse $ decompose globals probdelta dest















