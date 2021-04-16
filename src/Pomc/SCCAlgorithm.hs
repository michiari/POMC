{- |
   Module      : Pomc.SCC
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm ( Graph
                         , SummaryBody(..)
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
import Pomc.SetMap 
import Pomc.State(showStates)
import Pomc.Data(BitEncoding)
import qualified  Pomc.DoubleHashTable as DHT

import qualified Data.Stack.ST  as StackST 
import Control.Monad ( forM_, forM,foldM, mapM) 
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef') 
import Data.Maybe 

import Data.Set (Set) 
import qualified Data.Set as Set 

import GHC.Natural(naturalToInt)

import Data.Vector (Vector) 
import qualified Data.Vector as V 

import Data.Hashable

data Edge = Internal 
  { from :: Int
  ,  to  :: Int 
  } | Summary 
  { from :: Int
  ,   to :: Int
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
  } | SingleNode
  { getgnId  :: Int
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
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
type GabowStack s v = StackST.Stack s v

data Graph s state = Graph
  { idSeq           :: STRef s Int
  , nodeToGraphNode :: DHT.DoubleHashTable s (Key state) (Value state)
  , edges           :: STRef s (Set (Edge)) -- Set is not keyed in the monad, it needs a STRef
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GabowStack s Int -- for the Gabow algorithm
  , sStack          :: GabowStack s Int -- for the Gabow algorithm
  , initials        :: STRef s (Set (Int,Bool))
  , summaries       :: STRef s (Vector (Int, SummaryBody, Key state))
  }

newGraph :: (SatState state, Eq state, Hashable state, Show state) => Vector (Key state) -> ST.ST s (Graph s state)
newGraph initials = do
  newIdSequence <- newSTRef (1 :: Int)
  dht           <- DHT.empty  
  newSet        <- newSTRef (Set.empty)
  newCSequence  <- newSTRef (-1 :: Int)
  newBS         <- StackST.stackNew
  newSS         <- StackST.stackNew
  newInitials   <- newSTRef (Set.empty)
  newSummaries  <- newSTRef(V.empty)
  forM_ (initials) $ \key -> do 
    newId <- freshPosId newIdSequence
    DHT.insert dht key newId $ SingleNode {getgnId = newId, iValue = 0, node = key};
    modifySTRef' newInitials (Set.insert (newId,True))
  return $ Graph { idSeq = newIdSequence
                 , nodeToGraphNode = dht 
                 , edges = newSet 
                 , c = newCSequence
                 , bStack = newBS
                 , sStack = newSS
                 , initials = newInitials
                 , summaries = newSummaries
                }

----------------------------------------------------------------------------------------

-- the iValue is used in the Gabow algorithm
setgnIValue ::  Int -> GraphNode state -> GraphNode state 
setgnIValue new SCComponent { getgnId = gid, nodes = ns} = SCComponent{ getgnId = gid, iValue = new,nodes = ns} 
setgnIValue new SingleNode{getgnId = gid, node = n}      = SingleNode{getgnId = gid, iValue = new, node = n}

resetgnIValue :: GraphNode state -> GraphNode state 
resetgnIValue  = setgnIValue 0

updateSummaryBody :: Int -> Set Int -> SummaryBody -> SummaryBody
updateSummaryBody newId idents SummaryBody{firstNode = f, lastNode = l, bodyEdges = b} = 
  let sub n = if Set.member n idents 
                then newId 
                else n
      update Internal{from = f, to = t} = Internal{from = sub f, to = sub t}
      update Summary{from = f, to =t, body = b} = Summary{from = sub f, to = sub t, body = Set.map update b}
  in SummaryBody{firstNode = sub f, lastNode= sub l, bodyEdges = Set.map update b}

allUntil :: GabowStack s v -> [v] -> (v -> ST.ST s Bool)  -> ST.ST s [v]
allUntil stack acc cond  = do 
  topElem <- StackST.stackPeek stack
  condEval <- cond $ fromJust topElem 
  if condEval
    then do 
      forM_ (acc) $ StackST.stackPush stack
      return acc
    else do
      topPopped <- StackST.stackPop stack 
      allUntil stack ((fromJust topPopped):acc) cond 


-- unsafe
initialNodes :: (SatState state, Eq state, Hashable state, Show state) =>  Graph s state -> ST.ST s (Vector (Key state))
initialNodes graph = 
  let gnNode (SingleNode{node = n}) = Set.singleton n
      gnNode (SCComponent{nodes=ns})= ns
  in do 
    inSet <- readSTRef (initials graph)
    let inIdents = Set.map fst . Set.filter snd $ inSet
    gnNodesList <- DHT.lookupMap (nodeToGraphNode graph) (Set.toList inIdents) gnNode
    return $ V.fromList . Set.toList . Set.unions $ gnNodesList

-- unsafe: precond: the node is already there
alreadyVisited :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s Bool 
alreadyVisited graph k = do
  graphNode <- DHT.lookup (nodeToGraphNode graph) k
  return $ (iValue graphNode) /= 0

alreadyDiscovered :: (SatState state, Eq state, Hashable state, Show state) => Graph s state-> Key state-> ST.ST s Bool 
alreadyDiscovered graph key = do 
  ident <- DHT.lookupId (nodeToGraphNode graph) key
  if isJust ident
    then do 
          inSet <- readSTRef (initials graph)
          return $ not $ Set.member (fromJust ident, True) inSet
    else do 
          ident <- freshPosId $ idSeq graph
          let sn = SingleNode{getgnId = ident,iValue = 0, node = key }
          debug ("Inserting new single node: " ++ show sn ++ "\n") $ DHT.insert (nodeToGraphNode graph) key ident sn;
          return False



-- unsafe
visitNode :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
visitNode graph key = do
  gn <- DHT.lookup (nodeToGraphNode graph) key 
  visitGraphNode graph gn
  

visitGraphNode :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> GraphNode state -> ST.ST s ()
visitGraphNode graph gn = do 
  modifySTRef' (initials graph) $ \s -> if Set.member (getgnId gn, True) s
                                          then Set.insert (getgnId gn, False) . Set.delete (getgnId gn, True) $ s
                                          else s 
  StackST.stackPush (sStack graph) (getgnId gn);
  sSize <- StackST.stackSize $ sStack graph 
  DHT.modify (nodeToGraphNode graph) (getgnId gn) $ setgnIValue (naturalToInt sSize);
  StackST.stackPush (bStack graph) (naturalToInt sSize)

--unsafe
updateSCC :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
updateSCC graph key = do 
  gn <- DHT.lookup (nodeToGraphNode graph) key
  updateSCCInt graph (iValue gn) 

updateSCCInt :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Int -> ST.ST s ()
updateSCCInt graph iValue =  do 
  topElemB <- StackST.stackPeek (bStack graph)
  if (iValue  < 0) || (iValue  >= (fromJust topElemB)) 
    then  return ()
    else do
      StackST.stackPop (bStack graph);
      updateSCCInt graph iValue


-- safe
resolveSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Int, SummaryBody, Key state) -> ST.ST s (Int,Bool)
resolveSummary graph (fr, sb, key) = do 
  alrDir <- alreadyDiscovered graph key 
  ident <- DHT.lookupId (nodeToGraphNode graph) key
  modifySTRef' (edges graph) $ Set.insert $ Summary{from = fr, to = fromJust ident, 
                                                    body = Set.unions [
                                                    bodyEdges sb
                                                    , Set.singleton $ Internal {from = fr, to = firstNode sb}
                                                    , Set.singleton $ Internal {from = lastNode sb,to =   fromJust ident}]
                                                    } 
  return (fromJust ident, not $ alrDir)

-- this simply creates a Summary Body
-- unsafe
discoverSummaryBody :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> StateId state -> ST.ST s SummaryBody
discoverSummaryBody graph fr  = 
  let containsSId SingleNode{node = n} = fst n == fr 
      containsSId SCComponent{nodes=ns} = Set.member fr . Set.map fst $ ns
      untilcond = \ident -> DHT.lookupApply (nodeToGraphNode graph) ident containsSId 
      toEdges acc [e] = return acc 
      toEdges acc (x:y:xs) = do 
                              edgeSet <- readSTRef (edges graph) 
                              let foundEdges = Set.filter (\e -> from e == x && to e == y) edgeSet
                              toEdges (Set.union acc foundEdges) (y:xs) 
      mapToEdges edges = toEdges Set.empty edges                          
  in do  
    body <- allUntil (sStack graph) [] untilcond
    bodyE <- mapToEdges body 
    return $ SummaryBody{firstNode = head body, lastNode = last body, bodyEdges = bodyE}

-- unsafe 
discoverSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> SummaryBody ->  Key state -> ST.ST s ()
discoverSummary graph from body to = do 
  gnFrom <- DHT.lookup (nodeToGraphNode graph) from 
  modifySTRef' (summaries graph) $ V.cons (getgnId gnFrom, body, to)

-- unsafe
insertInternal :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> ST.ST s ()
insertInternal graph fromKey toKey  = do 
  fr <- DHT.lookupId (nodeToGraphNode graph) fromKey
  t  <- DHT.lookupId (nodeToGraphNode graph) toKey
  debug ("InsertInternal: from: " ++ show fr ++ "} ---> to: " ++ show t ++ "\n") $ modifySTRef' (edges graph) 
    $ Set.insert $ Internal (fromJust fr) (fromJust t)

-- unsafe
insertSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> SummaryBody -> ST.ST s ()
insertSummary graph fromKey toKey  sb = do 
  fr <- DHT.lookupId (nodeToGraphNode graph) fromKey
  t  <- DHT.lookupId (nodeToGraphNode graph) toKey
  let summ =  Summary{from = fromJust fr, to = fromJust t, 
                                                    body = Set.unions [
                                                    bodyEdges sb
                                                    , Set.singleton $ Internal {from = fromJust fr, to = firstNode sb}
                                                    , Set.singleton $ Internal {from = lastNode sb,to =   fromJust t}]
                                                    } 
  modifySTRef' (edges graph) $ Set.insert summ
  debug  ("InsertSummary: from: " ++ show fr ++ "} ---> to: " ++ show t ++ "edge: " ++ show summ ++ "\n") 
    $ modifySTRef' (edges graph) $ Set.insert $ Internal{from=(fromJust fr), to = firstNode sb};
                                           

createComponent :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Key state -> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponent graph key areFinal = do
  gn <- DHT.lookup (nodeToGraphNode graph) key
  debug ("Creating component for node: " ++ show gn) $ createComponentGn graph gn areFinal

createComponentGn :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> GraphNode state -> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponentGn graph gn areFinal = do
  topB <- StackST.stackPeek (bStack graph) 
  if  (iValue gn) == (fromJust topB)
    then do 
      StackST.stackPop (bStack graph)
      mergeComponents graph (iValue gn) Set.empty areFinal
    else return $ (False, Nothing) 

mergeComponents :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Int -> Set Int -> ([state] -> Bool)  -> ST.ST s (Bool, Maybe (Int, Set Int))
mergeComponents graph iValue  acc areFinal = do
  sSize <- StackST.stackSize $ sStack graph
  if iValue > naturalToInt sSize
    then merge graph (Set.toList acc) areFinal
    else do
      elem <- StackST.stackPop $ sStack graph
      mergeComponents graph iValue (Set.insert (fromJust elem) acc) areFinal 

merge :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> [Int] -> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
merge graph [ident]  areFinal = do
  newC <- freshNegId (c graph)
  DHT.modify (nodeToGraphNode graph) ident $ setgnIValue newC 
  edgeSet <- readSTRef (edges graph)
  let selfLoop = not . Set.null . Set.filter (\e -> from e == ident && to e == ident) $ edgeSet
  if selfLoop 
    then do 
      isA <- isAccepting graph ident areFinal
      return (isA, Nothing)
    else return $ (False, Nothing)
merge graph idents areFinal = 
  let 
    gnNode SingleNode{node = n}    = Set.singleton n
    gnNode SCComponent{nodes = ns} = ns
  in do 
    newC <- freshNegId (c graph)
    newId <- freshPosId (idSeq graph)
    gnsNodes <- DHT.lookupMap (nodeToGraphNode graph) idents gnNode
    let gnsNodesSet = Set.unions gnsNodes
        newgn = SCComponent{nodes = gnsNodesSet, getgnId = newId, iValue = newC}
        identsSet = Set.fromList idents
        sub n = if Set.member n identsSet 
                  then newId
                  else n 
        update Internal{from = f, to = t} = Internal{from = sub f, to = sub t}
        update Summary{from = f, to =t, body = b} = Summary{from = sub f, to = sub t, body = Set.map update b }       
    DHT.fuse (nodeToGraphNode graph) gnsNodesSet newId newgn;
    modifySTRef' (edges graph) $ Set.map update;
    modifySTRef' (summaries graph) $ V.map $ \(f,sb,t) -> (sub f, updateSummaryBody newId identsSet sb,t)
    modifySTRef' (initials graph)  $ Set.map $ \(n,b) -> (sub n,b)
    isA <- isAccepting graph newId areFinal
    return (isA, Just $ (newId, identsSet))

-- not safe
isAccepting :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> Int -> ([state] -> Bool) -> ST.ST s Bool
isAccepting graph ident areFinal = 
  let gnStates SingleNode{node = n} = Set.singleton . getState . fst $ n
      gnStates SCComponent{nodes= ns} = Set.map (getState . fst) ns
      edgeGnIdents Internal{from=fr, to=t}          = Set.fromList [fr,t]
      edgeGnIdents Summary{from= fr, to=t, body =b} = Set.union (Set.fromList [fr,t]) $ Set.unions (Set.map edgeGnIdents b)
      selfEdges = Set.filter (\e -> from e == ident && to e == ident)
  in do  
    edgeSet <- readSTRef (edges graph)
    gnStatesList <- DHT.lookupMap (nodeToGraphNode graph) (Set.toList . Set.unions . Set.map edgeGnIdents $ selfEdges edgeSet) gnStates
    return $ areFinal . Set.toList . Set.unions $ gnStatesList
    


summariesSize :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s Int
summariesSize graph = do
  summ <- readSTRef $ summaries graph
  return $ V.length summ

toCollapsePhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (Set (Int,Bool))
toCollapsePhase graph = do 
  DHT.modifyAll (nodeToGraphNode graph) resetgnIValue
  summ <- readSTRef $ summaries graph 
  newInitials <- forM (V.toList summ) $ resolveSummary graph
  modifySTRef' (initials graph) $ Set.map $ \(ident, _) -> (ident,True)
  return $ Set.fromList newInitials


toSearchPhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Set (Int,Bool)) -> ST.ST s ()
toSearchPhase graph newInitials = do 
  DHT.modifyAll (nodeToGraphNode graph) resetgnIValue
  writeSTRef (initials graph) newInitials;
  writeSTRef (summaries graph) V.empty

--unsafe
visitGraphFromKey :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> (Maybe(Int, Set Int) -> ST.ST s ()) -> ([state] -> Bool) -> Key state -> ST.ST s Bool 
visitGraphFromKey graph sbUpdater areFinal  key = do 
  gn <- DHT.lookup (nodeToGraphNode graph) key 
  visitGraphFrom graph sbUpdater areFinal gn 

-- unsafe
visitGraphFrom :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> (Maybe(Int, Set Int) -> ST.ST s ()) -> ([state] -> Bool) -> GraphNode state -> ST.ST s Bool 
visitGraphFrom graph sbUpdater areFinal  gn = do 
  visitGraphNode graph gn;
  edgeSet <- readSTRef (edges graph)
  let nextIdents = Set.toList $ Set.map (\e -> to e) $ Set.filter (\e -> from e == getgnId gn) edgeSet
  nextGns <- DHT.lookupMap (nodeToGraphNode graph) nextIdents id
  success <-  foldM (\acc gn -> if acc
                                  then return True 
                                  else if (iValue gn) == 0 
                                        then visitGraphFrom graph sbUpdater areFinal gn
                                        else  do 
                                          updateSCCInt graph (iValue gn)
                                          return False)                                          
                    False
                    nextGns 
  if success
    then return True 
    else  do 
      result <- createComponentGn graph gn areFinal
      sbUpdater $ snd result;
      return $ fst result