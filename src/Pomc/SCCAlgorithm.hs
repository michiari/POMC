{- |
   Module      : Pomc.SCC
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm ( Graph
                         , SummaryBody
                         , Edge
                         , newGraph
                         , alreadyDiscovered
                         , alreadyVisited
                         , visitGraphFromKey
                         , initialNodes
                         , summariesSize
                         , toCollapsePhase
                         , toSearchPhase
                         , visitNode
                         , createComponent
                         , discoverSummaryBody
                         , insertInternal
                         , insertSummary
                         , discoverSummary
                         , updateSummaryBody
                         , updateSCC
                         ) where

import Pomc.SatUtil
import qualified  Pomc.DoubleHashTable as DHT
import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import Control.Monad ( forM_, forM,foldM, mapM) 
import qualified Control.Monad.ST as ST

import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef') 
import Data.Maybe

import Data.Set (Set) 
import qualified Data.Set as Set 

import Data.Vector (Vector) 

import Data.Maybe(catMaybes)

import Data.Hashable

data Edge = Internal 
  { to  :: Int 
  } | Summary 
  { to :: Int
  ,  body :: Set (Edge) 
  } deriving (Show, Eq, Ord)

data SummaryBody = SummaryBody 
  { firstNode :: Int
  , lastNode  :: Int 
  , bodyEdges :: Set (Edge)
  } deriving (Show,Eq,Ord)

data GraphNode state = SCComponent
  { getgnId   :: Int -- immutable
  , iValue    :: Int -- changes at each iteration of the Gabow algorithm
  , nodes     :: Set (StateId state, Stack state)
  , edges     :: Set Edge
  } | SingleNode
  { getgnId  :: Int
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
  , edges    :: Set Edge
  } 

instance (Show state) => Show (GraphNode  state) where
  show gn =  show $ getgnId gn 

instance Eq (GraphNode state) where
  p == q = getgnId p == getgnId q

instance  Ord (GraphNode state) where
  compare p q = compare (getgnId p) (getgnId q)

instance Hashable (GraphNode state) where
  hashWithSalt salt s = hashWithSalt salt $ (getgnId s) 

type Key state = (StateId state, Stack state)
type Value state = GraphNode state

data Graph s state = Graph
  { idSeq           :: STRef s Int
  , nodeToGraphNode :: DHT.DoubleHashTable s (Key state) (Value state)
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GStack s Int -- for the Gabow algorithm
  , sStack          :: GStack s (Maybe Edge, Int) -- for the Gabow algorithm
  , initials        :: STRef s (Set (Int,Bool))
  , summaries       :: STRef s (Set (Int, SummaryBody, Key state))
  }

newGraph :: (SatState state, Eq state, Hashable state, Show state) 
            => Vector (Key state) 
            -> ST.ST s (Graph s state)
newGraph iniNodes = do
  newIdSequence <- newSTRef (1 :: Int)
  dht           <- DHT.empty  
  newCSequence  <- newSTRef (-1 :: Int)
  newBS         <- GS.new
  newSS         <- GS.new
  newInitials   <- newSTRef (Set.empty)
  newSummaries  <- newSTRef (Set.empty)
  forM_ (iniNodes) $ \key -> do 
    newId <- freshPosId newIdSequence
    DHT.insert dht key newId $ SingleNode {getgnId = newId, iValue = 0, node = key, edges = Set.empty};
    modifySTRef' newInitials (Set.insert (newId,True))
  return $ Graph { idSeq = newIdSequence
                 , nodeToGraphNode = dht 
                 , c = newCSequence
                 , bStack = newBS
                 , sStack = newSS
                 , initials = newInitials
                 , summaries = newSummaries
                }

----------------------------------------------------------------------------------------
-- the iValue is used in the Gabow algorithm
setgnIValue ::  Int -> GraphNode state -> GraphNode state 
setgnIValue new gn@SCComponent{} = gn{iValue = new} 
setgnIValue new gn@SingleNode{}  = gn{iValue = new}

resetgnIValue :: GraphNode state -> GraphNode state 
resetgnIValue  = setgnIValue 0

updateSummaryBody :: Int -> Set Int -> SummaryBody -> SummaryBody
updateSummaryBody newId idents SummaryBody{firstNode = f, lastNode = l, bodyEdges = b} = 
  let sub n = if Set.member n idents 
                then newId 
                else n
      update Internal{to = t} = Internal{ to = sub t}
      update Summary{to =t, body = summB} = Summary{to = sub t, body = Set.map update summB}
  in SummaryBody{firstNode = sub f, lastNode= sub l, bodyEdges = Set.map update b}

-- unsafe
initialNodes :: (SatState state, Eq state, Hashable state, Show state) 
                =>  Graph s state 
                -> ST.ST s (Set (Key state))
initialNodes graph = 
  let gnNode (SingleNode{node = n}) = Set.singleton n
      gnNode (SCComponent{nodes=ns})= ns
  in do 
    inSet <- readSTRef $ initials graph
    let inIdents = Set.map fst . Set.filter snd $ inSet
    gnNodesList <- DHT.lookupMap (nodeToGraphNode graph) (Set.toList inIdents) gnNode
    return $ Set.unions gnNodesList

-- unsafe
alreadyVisited :: (SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Key state 
                  -> ST.ST s Bool 
alreadyVisited graph k = do
  graphNode <- DHT.lookup (nodeToGraphNode graph) k
  return $ (iValue graphNode) /= 0

alreadyDiscovered :: (SatState state, Eq state, Hashable state, Show state) 
                     => Graph s state 
                     -> Key state 
                     -> ST.ST s Bool 
alreadyDiscovered graph key = do 
  ident <- DHT.lookupId (nodeToGraphNode graph) key
  if isJust ident
    then do 
      inSet <- readSTRef (initials graph)
      return $ not $ Set.member (fromJust ident, True) inSet
    else do 
      newIdent <- freshPosId $ idSeq graph
      let sn = SingleNode{getgnId = newIdent,iValue = 0, node = key, edges = Set.empty}
      DHT.insert (nodeToGraphNode graph) key newIdent sn;
      return False

-- unsafe
visitNode :: (SatState state, Eq state, Hashable state, Show state) 
              => Graph s state 
              -> Maybe Edge 
              -> Key state 
              -> ST.ST s ()
visitNode graph e key = do
  gn <- DHT.lookup (nodeToGraphNode graph) key 
  visitGraphNode graph e gn 
  

visitGraphNode :: (SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Maybe Edge 
                  -> GraphNode state 
                  -> ST.ST s ()
visitGraphNode graph e gn = do 
  modifySTRef' (initials graph) 
    $ \s -> if Set.member (getgnId gn, True) s
              then Set.insert (getgnId gn, False) . Set.delete (getgnId gn, True) $ s
              else s 
  GS.push (sStack graph) (e, getgnId gn);
  sSize <- GS.size $ sStack graph 
  DHT.modify (nodeToGraphNode graph) (getgnId gn) $ setgnIValue sSize;
  GS.push (bStack graph) sSize

--unsafe
updateSCC :: (SatState state, Eq state, Hashable state, Show state) 
              => Graph s state 
              -> Key state 
              -> ST.ST s ()
updateSCC graph key = do 
  gn <- DHT.lookup (nodeToGraphNode graph) key
  updateSCCInt graph (iValue gn) 

updateSCCInt :: (SatState state, Eq state, Hashable state, Show state) 
                => Graph s state 
                -> Int 
                -> ST.ST s ()
updateSCCInt graph iVal =  do 
  topElemB <- GS.peek (bStack graph)
  if (iVal  < 0) || (iVal  >=  topElemB) 
    then  return ()
    else do
      _ <- GS.pop (bStack graph);
      updateSCCInt graph iVal

-- unsafe
discoverSummaryBody :: (SatState state, Eq state, Hashable state, Show state) 
                        => Graph s state 
                        -> StateId state 
                        -> ST.ST s SummaryBody
discoverSummaryBody graph fr  = 
  let containsSId SingleNode{node = n} = fst n == fr 
      containsSId SCComponent{nodes=ns} = Set.member fr . Set.map fst $ ns
      untilcond = \(_,ident) -> DHT.lookupApply (nodeToGraphNode graph) ident containsSId   
      mapToEdges (_:xs) = Set.fromList . catMaybes .  map fst $ xs                 
  in do  
    b <- GS.allUntil (sStack graph) untilcond
    return $ SummaryBody{firstNode =  snd . head $ b, lastNode = snd . last $ b, bodyEdges = mapToEdges b}

-- unsafe 
discoverSummary :: (SatState state, Eq state, Hashable state, Show state) 
                    => Graph s state -> Key state 
                    -> SummaryBody 
                    -> Key state 
                    -> ST.ST s ()
discoverSummary graph fr b t = do 
  gnFrom <- DHT.lookup (nodeToGraphNode graph) fr 
  modifySTRef' (summaries graph) $ Set.insert (getgnId gnFrom, b, t)

-- unsafe
insertInternal :: (SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Key state 
                  -> Key state 
                  -> ST.ST s Edge
insertInternal graph fromKey toKey  = do 
  fr <- DHT.lookupId (nodeToGraphNode graph) fromKey
  t  <- DHT.lookupId (nodeToGraphNode graph) toKey
  let e = Internal (fromJust t)
      insertEdge x@SingleNode{edges = es}  = x{edges = Set.insert e es}
      insertEdge x@SCComponent{edges = es} = x{edges = Set.insert e es}
  DHT.modify (nodeToGraphNode graph) (fromJust fr) insertEdge;
  return e

-- unsafe
insertSummary :: (SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Key state 
                  -> Key state 
                  -> SummaryBody 
                  -> ST.ST s Edge
insertSummary graph fromKey toKey  sb = do 
  fr <- DHT.lookupId (nodeToGraphNode graph) fromKey
  t  <- DHT.lookupId (nodeToGraphNode graph) toKey
  let summ =  Summary{ to = fromJust t, body = bodyEdges sb } 
      e = Internal{ to = firstNode sb}
      insertEdges x@SingleNode{edges = es}  = x{edges = Set.insert summ $ Set.insert e es}
      insertEdges x@SCComponent{edges = es} = x{edges = Set.insert summ $ Set.insert e es}
  DHT.modify (nodeToGraphNode graph) (fromJust fr) insertEdges
  return e
                                           
createComponent :: (SatState state, Ord state, Hashable state, Show state) 
                    => Graph s state 
                    -> Key state 
                    -> ([state] -> Bool) 
                    -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponent graph key areFinal = do
  gn <- DHT.lookup (nodeToGraphNode graph) key
  createComponentGn graph gn areFinal

createComponentGn :: (SatState state, Ord state, Hashable state, Show state) 
                      => Graph s state 
                      -> GraphNode state 
                      -> ([state] -> Bool) 
                      -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponentGn graph gn areFinal = 
  let 
    toMerge [ident] = do 
      newC <- freshNegId (c graph)
      DHT.modify (nodeToGraphNode graph) ident $ setgnIValue newC  
      let selfLoopOrGn SingleNode{edges =es} = not . Set.null . Set.filter (\e -> to e == ident) $ es
          selfLoopOrGn SCComponent{}  = True 
      if selfLoopOrGn gn 
        then do 
          isA <- isAccepting graph ident areFinal
          return (isA, Nothing)
        else return $ (False, Nothing)
    toMerge idents = merge graph idents areFinal
    findComponents acc = do 
      sSize <- GS.size $ sStack graph
      if (iValue gn) > sSize
        then toMerge $ Set.toList acc
        else do
          popped <- GS.pop $ sStack graph
          findComponents (Set.insert (snd popped) acc)  
  in do
    topB <- GS.peek (bStack graph) 
    if  (iValue gn) == topB
      then do 
        _ <- GS.pop (bStack graph)
        findComponents Set.empty 
      else return $ (False, Nothing) 

merge :: (SatState state, Ord state, Hashable state, Show state) 
          => Graph s state  
          -> [Int] 
          -> ([state] -> Bool) 
          -> ST.ST s (Bool, Maybe (Int, Set Int))
merge graph idents areFinal = 
  let 
    gnNode SingleNode{node = n}    = Set.singleton n
    gnNode SCComponent{nodes = ns} = ns
  in do 
    newC <- freshNegId (c graph)
    newId <- freshPosId (idSeq graph)
    gnsNodes <- DHT.lookupMap (nodeToGraphNode graph) idents gnNode
    gnsEdges <- DHT.lookupMap (nodeToGraphNode graph) idents edges
    let gnsNodesSet = Set.unions gnsNodes
        gnsEdgesSet = Set.unions gnsEdges
        newgn = SCComponent{nodes = gnsNodesSet, getgnId = newId, iValue = newC, edges = gnsEdgesSet}
        identsSet = Set.fromList idents
        sub n = if Set.member n identsSet 
                  then newId
                  else n 
        update Internal{ to = t} = Internal{ to = sub t}
        update Summary{ to =t, body = b} = Summary{ to = sub t, body = Set.map update b } 
        updateGn x@SingleNode{edges = es}  = x{edges = Set.map update es}   
        updateGn x@SCComponent{edges = es} = x{edges = Set.map update es}     
    DHT.fuse (nodeToGraphNode graph) gnsNodesSet newId newgn;
    DHT.modifyAll (nodeToGraphNode graph) updateGn
    modifySTRef' (summaries graph) $ Set.map $ \(f,sb,t) -> (sub f, updateSummaryBody newId identsSet sb,t)
    modifySTRef' (initials graph)  $ Set.map $ \(n,b) -> (sub n,b)
    isA <- isAccepting graph newId areFinal
    return (isA, Just $ (newId, identsSet))

-- not safe
isAccepting :: (SatState state, Ord state, Hashable state, Show state) 
                => Graph s state 
                -> Int 
                -> ([state] -> Bool) 
                -> ST.ST s Bool
isAccepting graph ident areFinal = 
  let gnStates SingleNode{node = n} = Set.singleton . getState . fst $ n
      gnStates SCComponent{nodes= ns} = Set.map (getState . fst) ns
      edgeGnIdents Internal{ to=t} = Set.singleton t
      edgeGnIdents Summary{to=t, body =b} = Set.union (Set.singleton t) $ Set.unions (Set.map edgeGnIdents b)
      selfEdges = Set.filter (\e -> to e == ident)
  in do  
    edgeSet <- DHT.lookupApply (nodeToGraphNode graph) ident edges
    gnStatesList <- DHT.lookupMap (nodeToGraphNode graph) (Set.toList . Set.unions . Set.map edgeGnIdents $ selfEdges edgeSet) gnStates
    return $ areFinal . Set.toList . Set.unions $ gnStatesList
    
summariesSize :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s Int
summariesSize graph = do
  summ <- readSTRef $ summaries graph
  return $ Set.size summ

toCollapsePhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (Set (Int,Bool))
toCollapsePhase graph = 
  let resolveSummary (fr, sb, key) = do  
        alrDir <- alreadyDiscovered graph key 
        ident <- DHT.lookupId (nodeToGraphNode graph) key
        let summ = Summary{ to = fromJust ident, body = bodyEdges sb}
            insertEdge x@SingleNode{edges = es}  = x{edges = Set.insert summ es}
            insertEdge x@SCComponent{edges = es} = x{edges = Set.insert summ es}
        DHT.modify (nodeToGraphNode graph) fr insertEdge
        return (fromJust ident, not $ alrDir)
  in do 
    DHT.modifyAll (nodeToGraphNode graph) resetgnIValue
    summ <- readSTRef $ summaries graph 
    newInitials <- mapM resolveSummary $ Set.toList summ
    modifySTRef' (initials graph) $ Set.map $ \(ident, _) -> (ident,True)
    return $ Set.fromList newInitials

toSearchPhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Set (Int,Bool)) -> ST.ST s ()
toSearchPhase graph newInitials = do 
  DHT.modifyAll (nodeToGraphNode graph) resetgnIValue
  writeSTRef (initials graph) newInitials;
  writeSTRef (summaries graph) Set.empty

--unsafe
visitGraphFromKey :: (SatState state, Ord state, Hashable state, Show state) 
                      => Graph s state 
                      -> (Maybe(Int, Set Int) -> ST.ST s ()) 
                      -> ([state] -> Bool) 
                      -> Maybe Edge 
                      -> Key state 
                      ->  ST.ST s Bool 
visitGraphFromKey graph sbUpdater areFinal e key = do 
  gn <- DHT.lookup (nodeToGraphNode graph) key 
  visitGraphFrom graph sbUpdater areFinal e gn 

-- unsafe
visitGraphFrom :: (SatState state, Ord state, Hashable state, Show state) 
                  => Graph s state 
                  -> (Maybe(Int, Set Int) 
                  -> ST.ST s ()) -> ([state] -> Bool) 
                  -> Maybe Edge 
                  -> GraphNode state 
                  -> ST.ST s Bool 
visitGraphFrom graph sbUpdater areFinal e gn  = do 
  visitGraphNode graph e gn;
  success <-  foldM (\acc nextEdge -> if acc
                                        then return True 
                                        else do 
                                          nextGn <- DHT.lookupApply (nodeToGraphNode graph) (to nextEdge) id
                                          if (iValue nextGn) == 0 
                                            then visitGraphFrom graph sbUpdater areFinal (Just nextEdge) nextGn
                                            else  do 
                                              updateSCCInt graph (iValue nextGn)
                                              return False)                                          
                    False
                    (edges gn)
  if success
    then return True 
    else  do 
      result <- createComponentGn graph gn areFinal
      sbUpdater $ snd result;
      return $ fst result