{- |
   Module      : Pomc.Prob.SupportGraph
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.SupportGraph ( SupportGraph
                              , buildGraph
                              , asPendingSemiconfs
                              , GraphNode(..)
                              , Edge(..)
                              ) where
import Pomc.Prob.ProbUtils
import Pomc.Prec (Prec(..))

import qualified Pomc.CustoMap as CM

import Pomc.SetMap(SetMap)
import qualified Pomc.SetMap as SM

import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Vector.Mutable as MV

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Control.Monad(forM, forM_, when)
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

buildGraph  :: (Eq state, Hashable state, Show state)
        => DeltaWrapper state -- probabilistic delta relation of a popa
        -> state -- initial state of the popa
        -> Label -- label of the initial state
        -> ST s (SupportGraph s state) -- returning a graph
buildGraph probdelta i iLabel = do
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
  build globals probdelta initialNode
  idx <- readSTRef . idSeq $ globals
  fmap (CM.take idx) $ readSTRef . graph $ globals

-- requires: the initial state of the OPA is mapped to StateId with getId 0
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

        | otherwise = return ()
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
  let doPush (p, pLabel, prob_) = do
        newState <- wrapState (sIdGen globals) p pLabel
        buildTransition globals probdelta (q,g) False
          prob_ (newState, Just (qLabel, q))
  in do
    SM.insert (suppStarts globals) (getId q) g
    mapM_ doPush $ (deltaPush probdelta) qState
    currentSuppEnds <- SM.lookup (suppEnds globals) (getId q)
    mapM_ (\s -> buildTransition globals probdelta (q,g) True 0 (s,g))  -- summaries are by default assigned probability zero
      currentSuppEnds

buildShift :: (Eq state, Hashable state, Show state)
           => Globals s state
           -> DeltaWrapper state
           -> StateId state
           -> Stack state
           -> state
           -> Label
           -> ST s ()
buildShift globals probdelta q g qState qLabel =
  let doShift (p, pLabel, prob_)= do
        newState <- wrapState (sIdGen globals) p pLabel
        buildTransition globals probdelta (q,g) False prob_ (newState, Just (qLabel, snd . fromJust $ g))
  in mapM_ doShift $ (deltaShift probdelta) qState

buildPop :: (Eq state, Hashable state, Show state)
         => Globals s state
         -> DeltaWrapper state
         -> StateId state
         -> Stack state
         -> state
         -> ST s ()
buildPop globals probdelta q g qState =
  let doPop (p, pLabel, prob_) =
        let r = snd . fromJust $ g
            closeSupports pwrapped g' = buildTransition globals probdelta (r,g') True prob_ (pwrapped, g')
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
buildTransition :: (Eq state, Hashable state, Show state)
                 => Globals s state
                 -> DeltaWrapper state
                 -> (StateId state, Stack state) -- from semiconf 
                 -> Bool -- is Support
                 -> Prob
                 -> (StateId state, Stack state) -- to semiconf
                 -> ST s ()
buildTransition globals probdelta from isSupport prob_ dest =
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
    when (isNothing maybeId) $ build globals probdelta dest

-- some renaming to make the algorithm more understandable
type CanReachPop = Bool
type Arch = Int

data DeficientGlobals s state = DeficientGlobals
  { supportGraph :: SupportGraph s state
  , sStack     :: GStack s Arch
  , bStack     :: GStack s Int
  , iVector    :: MV.MVector s Int
  , canReachPop :: MV.MVector s CanReachPop
  }

-- TODO: maybe return something like a list... I don't know
asPendingSemiconfs :: Show state => SupportGraph s state -> ST s IntSet
asPendingSemiconfs suppGraph = do
  newSS            <- GS.new
  newBS            <- GS.new
  newIVec          <- MV.replicate (MV.length suppGraph) 0
  newCanReachPop <- MV.replicate (MV.length suppGraph) False
  let globals = DeficientGlobals { supportGraph = suppGraph
                                 , sStack = newSS
                                 , bStack = newBS
                                 , iVector = newIVec
                                 , canReachPop = newCanReachPop
                                 }
  -- perform the Gabow algorithm to determine semiconfs that cannot reach a pop
  gn <- MV.unsafeRead suppGraph 0
  addtoPath globals gn
  _ <- dfs globals gn
  let f acc _ True = acc
      f acc idx False = IntSet.insert idx acc
  MV.ifoldl' f IntSet.empty (canReachPop globals)

dfs :: Show state => DeficientGlobals s state
    -> GraphNode state
    -> ST s CanReachPop
dfs globals gn =
  let cases nextNode iVal
        | (iVal == 0) = addtoPath globals nextNode >> dfs globals nextNode
        | (iVal < 0)  = MV.unsafeRead (canReachPop globals) (gnId nextNode)
        -- here we don't need the additional push of the closing edge
        | (iVal > 0)  = merge globals nextNode >> return False
        | otherwise = error "unreachable error"
      follow e = do
        node <- MV.unsafeRead (supportGraph globals) (to e)
        iVal <- MV.unsafeRead (iVector globals) (to e)
        cases node iVal
  in do
    descendantsCanReachPop <- or <$> forM (Set.toList $ internalEdges gn) follow
    let computeActualCanReach
          | not . Set.null $ supportEdges gn =  or <$> forM (Set.toList $ supportEdges gn) follow
          | not . Map.null $ popContexts gn = return True
          | otherwise = return descendantsCanReachPop
    canReach <- computeActualCanReach
    createComponent globals gn canReach

-- helpers
addtoPath :: DeficientGlobals s state -> GraphNode state -> ST s ()
addtoPath globals gn = do
  GS.push (sStack globals) (gnId gn)
  sSize <- GS.size $ sStack globals
  MV.unsafeWrite (iVector globals) (gnId gn) sSize
  GS.push (bStack globals) sSize

merge ::  DeficientGlobals s state -> GraphNode state -> ST s ()
merge globals gn = do
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  GS.popWhile_ (bStack globals) (iVal <)


createComponent :: DeficientGlobals s state -> GraphNode state -> CanReachPop -> ST s CanReachPop
createComponent globals gn canReachP = do
  topB <- GS.peek $ bStack globals
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  if iVal == topB
    then do
      GS.pop_ (bStack globals)
      sSize <- GS.size $ sStack globals
      poppedEdges <- GS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
      forM_ poppedEdges $ \e -> do
        MV.unsafeWrite (iVector globals) e (-1)
        MV.unsafeWrite (canReachPop globals) e canReachP
      return canReachP
    else do
      return canReachP
