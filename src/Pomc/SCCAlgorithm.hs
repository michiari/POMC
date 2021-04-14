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
                         , visitGraphFrom
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
 -- TODO. optimize imports
import Pomc.SatUtils 
import Pomc.State(showStates)
import Pomc.Data(BitEncoding)
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
import Data.List(nub)

import Debug.Trace (trace)

import Data.Hashable

data Edge = Internal 
  { from :: Int
  ,  to  :: Int 
  } | Summary 
  { from :: Int
  ,   to :: Int
  ,  body :: Set (Edge) 
  } deriving (Show, Eq, Ord)

-- the nodes which form a  summary body
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
  { getgnId  :: Int -- immutable
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
  , nodeToGraphNode :: DoubleHashTable s (Key state) (Value state)
  , edges           :: STRef s (Set (Edge)) -- Set is not keyed in the monad, it needs a STRef
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GabowStack s Int -- for the Gabow algorithm
  , sStack          :: GabowStack s Int -- for the Gabow algorithm
  , initials        :: STRef s (TwinSet Int)
  , summaries       :: STRef s (Vector (Int -> Edge, Key state))
  }

----------------------------------------------------------------------------------------

    
-- the iValue is used in the Gabow algorithm
setgnIValue ::  Int -> GraphNode state -> GraphNode state 
setgnIValue new SCComponent { getgnId = gid, nodes = ns} = SCComponent{ getgnId = gid, iValue = new,nodes = ns} 
setgnIValue new SingleNode{getgnId = gid, node = n}      = SingleNode{getgnId = gid, iValue = new, node = n}

resetgnIValue :: GraphNode state -> GraphNode state 
resetgnIValue  = setgnIValue 0

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return $ curr

freshNegId :: STRef s Int -> ST.ST s Int
freshNegId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+(-1));
  return $ curr

lookupEdges :: STRef s (Set (Edge)) -> Int -> Int -> ST.ST s (Set (Edge))
lookupEdges edgeref fr t = do
  edgeSet <- readSTRef edgeref
  return $  Set.filter (\e -> from e == fr && to e == t) edgeSet 

selfLoop ::  STRef s (Set (Edge)) -> Int -> ST.ST s Bool
selfLoop edgeref ident = do
  selfEdges <- lookupEdges edgeref ident ident 
  return $ not $ Set.null selfEdges 

-- this is used in let it run
nextStepsFrom :: STRef s (Set (Edge)) -> Int -> ST.ST s (Set  Int)
nextStepsFrom edgeref fr  = do
  edgeSet <- readSTRef edgeref
  return $ Set.map (\e -> to e) $ Set.filter (\e -> from e == fr) edgeSet

-- map a list of nodes to the set of edges which connect them
toEdges :: STRef s (Set (Edge)) -> Set Edge -> [Int] -> ST.ST s (Set Edge)
toEdges edgeref acc [x] = return acc
toEdges edgeref acc (x:y:xs) = do 
                                found <- lookupEdges edgeref x y 
                                toEdges edgeref  (Set.union acc found) (y:xs)

updateEdge :: Set Int -> Int -> Edge -> Edge 
updateEdge idents newId e = 
  let sub n = if Set.member n idents 
                then newId
                else n
      update Internal{from = f, to = t} = Internal{from = sub f, to = sub t}
      update Summary{from = f, to =t, body = b} = Summary{from = sub f, to = sub t, body = Set.map update b }
  in update e 

updateEdges :: STRef s (Set (Edge)) -> Set Int -> Int -> ST.ST s ()
updateEdges edgeref idents newId = modifySTRef' edgeref $ Set.map $ updateEdge idents newId

-- TODO: exchange parameters of this!
updateSummaryBody :: Int -> Set Int -> SummaryBody -> SummaryBody
updateSummaryBody newId idents SummaryBody{firstNode = f, lastNode = l, bodyEdges = b} = 
  let sub n = if Set.member n idents 
                then newId 
                else n
  in SummaryBody{firstNode = sub f, lastNode= sub l, bodyEdges = Set.map (updateEdge idents newId) b}

buildSummary :: Int -> SummaryBody -> Int -> Edge 
buildSummary fr sb t  = Summary {from = fr, to = t, 
                                  body = Set.unions [
                                    bodyEdges sb
                                  , Set.singleton $ Internal {from = fr, to = firstNode sb}
                                  , Set.singleton $ Internal {from = lastNode sb,to = t   }]
                                }

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

newGraph :: (SatState state, Eq state, Hashable state, Show state) => Vector (Key state) -> ST.ST s (Graph s state)
newGraph initials = do
  newIdSequence <- newSTRef (0 :: Int)
  dht           <- emptyDHT  
  newSet        <- newSTRef (Set.empty)
  newCSequence  <- newSTRef (-1 :: Int)
  newBS         <- StackST.stackNew
  newSS         <- StackST.stackNew
  newInitials   <- emptyTS
  newSummaries  <- newSTRef(V.empty)
  initialsIds  <- forM (initials) $ \key -> do 
                  newId <- freshPosId newIdSequence
                  insertDHT dht key newId $ SingleNode {getgnId = newId, iValue = 0, node = key};
                  return newId
  initializeTS  newInitials $ Set.fromList $ V.toList initialsIds;
  return $ Graph { idSeq = newIdSequence
                 , nodeToGraphNode = dht 
                 , edges = newSet 
                 , c = newCSequence
                 , bStack = newBS
                 , sStack = newSS
                 , initials = newInitials
                 , summaries = newSummaries
                }

-- unsafe
initialNodes :: (SatState state, Eq state, Hashable state, Show state) => BitEncoding -> Graph s state -> ST.ST s (Vector (Key state))
initialNodes bitenc graph = 
  let gnNode (SingleNode{node = n}) = Set.singleton n
      gnNode (SCComponent{nodes=ns})= ns
  in do 
    inIdents <- valuesTS $ initials graph
    gnNodesList <- lookupApplyMultDHT (nodeToGraphNode graph) (Set.toList inIdents) gnNode
    let results =  Set.toList . Set.unions $ gnNodesList
        satStates = map (getSatState . getState . fst) results
    debug ("Initial nodes of this search phase: " ++ (showStates bitenc satStates) ++ "\n\n" ++ show results) $ return $ V.fromList results 


-- unsafe: precond: the node is already there
alreadyVisited :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s Bool 
alreadyVisited graph k = do
  graphNode <- lookupDHT (nodeToGraphNode graph) k
  return $ (iValue graphNode) /= 0

alreadyDiscovered :: (SatState state, Eq state, Hashable state, Show state) => Graph s state-> Key state-> ST.ST s Bool 
alreadyDiscovered graph key = do 
  ident <- lookupIdDHT (nodeToGraphNode graph) key
  if isJust ident
    then do 
          isMarked <- isMarkedTS (initials graph) $ fromJust ident
          return $ not isMarked 
    else do 
          ident <- freshPosId $ idSeq graph
          let sn = SingleNode{getgnId = ident,iValue = 0, node = key }
          debug ("Inserting new single node: " ++ show sn ++ "\n") $ insertDHT (nodeToGraphNode graph) key ident sn;
          return False



-- unsafe
visitNode :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
visitNode graph key = do
  gn <- lookupDHT (nodeToGraphNode graph) key 
  visitNode' graph gn
  

visitNode' :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> GraphNode state -> ST.ST s ()
visitNode' graph gn = do 
  unmarkTS (initials graph) $ getgnId gn;
  StackST.stackPush (sStack graph) (getgnId gn);
  sSize <- StackST.stackSize $ sStack graph 
  modifyDHT (nodeToGraphNode graph) (getgnId gn) $ setgnIValue (naturalToInt sSize);
  StackST.stackPush (bStack graph) (naturalToInt sSize)

--unsafe
updateSCC :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
updateSCC graph key = do 
  gn <- lookupDHT (nodeToGraphNode graph) key
  updateSCC' graph (iValue gn) 

updateSCC' :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Int -> ST.ST s ()
updateSCC' graph iValue =  do 
  topElemB <- StackST.stackPeek (bStack graph)
  if (iValue  < 0) || (iValue  >= (fromJust topElemB)) 
    then  return ()
    else do
      StackST.stackPop (bStack graph);
      updateSCC' graph iValue


-- safe
resolveSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Int -> Edge, Key state) -> ST.ST s (Bool, Int)
resolveSummary graph (builder, key) = do 
  alrDir <- alreadyDiscovered graph key 
  ident <- lookupIdDHT (nodeToGraphNode graph) key
  modifySTRef' (edges graph) $ Set.insert $ builder $ fromJust ident;
  return (alrDir, fromJust ident)

-- this simply creates a Summary Body
-- unsafe
discoverSummaryBody :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> StateId state -> ST.ST s SummaryBody
discoverSummaryBody graph from  = 
  let containsSId SingleNode{node = n} = fst n == from 
      containsSId SCComponent{nodes=ns} = Set.member from . Set.map fst $ ns
      untilcond = \ident -> lookupApplyDHT (nodeToGraphNode graph) ident containsSId                            
  in do  
    body <- allUntil (sStack graph) [] untilcond
    edgeSet <- toEdges (edges graph) Set.empty body 
    return $ SummaryBody{firstNode = head body, lastNode = last body, bodyEdges = edgeSet}

-- unsafe 
discoverSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> SummaryBody ->  Key state -> ST.ST s ()
discoverSummary graph from body to = do 
  gnFrom <- lookupDHT (nodeToGraphNode graph) from 
  modifySTRef' (summaries graph) $ V.cons (\toInt -> buildSummary (getgnId gnFrom) body toInt, to)

-- unsafe
insertInternal :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> ST.ST s ()
insertInternal graph fromKey toKey  = do from <- lookupIdDHT (nodeToGraphNode graph) fromKey
                                         to   <- lookupIdDHT (nodeToGraphNode graph) toKey
                                         debug ("InsertInternal: from: " ++ show from ++ "} ---> to: " ++ show to ++ "\n") $ modifySTRef' (edges graph) $ Set.insert $ Internal (fromJust from) (fromJust to)

-- unsafe
insertSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> SummaryBody -> ST.ST s ()
insertSummary graph fromKey toKey  sb = do fr <- lookupIdDHT (nodeToGraphNode graph) fromKey
                                           t  <- lookupIdDHT (nodeToGraphNode graph) toKey
                                           let summ =  buildSummary (fromJust fr) sb (fromJust t)
                                           modifySTRef' (edges graph) $ Set.insert summ
                                           debug  ("InsertSummary: from: " ++ show fr ++ "} ---> to: " ++ show t ++ "edge: " ++ show summ ++ "\n") $ modifySTRef' (edges graph) $ Set.insert $ Internal{from=(fromJust fr), to = firstNode sb};
                                           -- TODO: ricorda che qui non hai inserito l'edge lastNode - to


-- the same as CreateComponent in the algorithm
-- TODO: update these functions' names to make the code more readable
createComponent :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Key state -> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponent graph key areFinal = do
  gn <- lookupDHT (nodeToGraphNode graph) key
  debug ("creating component for node: " ++ show gn) $ createComponent' graph gn areFinal

createComponent' :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> GraphNode state -> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
createComponent' graph gn areFinal = do
  topB <- StackST.stackPeek (bStack graph) 
  if  (iValue gn) == (fromJust topB)
    then do 
      StackST.stackPop (bStack graph)
      mergeComponents graph (iValue gn) Set.empty areFinal
    else return $ (False, Nothing) 

mergeComponents :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Int -> Set Int -> ([state] -> Bool)  -> ST.ST s (Bool, Maybe (Int, Set Int))
mergeComponents graph iValue  acc areFinal = do
  sSize <- StackST.stackSize (sStack graph)
  if iValue > (naturalToInt sSize)
    then do 
      gnList <- lookupApplyMultDHT (nodeToGraphNode graph) (Set.toList acc) id
      dotheMerge graph gnList areFinal
    else do
      elem <- StackST.stackPop (sStack graph)
      mergeComponents graph iValue (Set.insert (fromJust elem) acc) areFinal
 
-- TODO: update this to optimize the case when we have a single SCComponent
dotheMerge :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> [GraphNode state]-> ([state] -> Bool) -> ST.ST s (Bool, Maybe (Int, Set Int))
dotheMerge graph [gn]  areFinal = do
  newC <- freshNegId (c graph)
  modifyDHT (nodeToGraphNode graph) (getgnId gn) $ setgnIValue newC 
  self <- selfLoop (edges graph) (getgnId gn)
  if self 
    then debug ("Single Node with Cycle found: " ++ show (setgnIValue newC gn) ++ "\n") $ do 
                                                                                            isA <- isAccepting graph gn areFinal
                                                                                            return (isA, Nothing)
    else debug ("Single Node without Cycle found: " ++ show (setgnIValue newC gn) ++ "\n") $ return $ (False, Nothing)
dotheMerge graph gns areFinal = 
  let 
    gnNode SingleNode{node = n}    = Set.singleton n
    gnNode SCComponent{nodes = ns} = ns
    gnsNodes = Set.unions . map gnNode $ gns
    oldIdents = Set.fromList . map getgnId $ gns
  in do 
    newC <- freshNegId (c graph)
    newId <- freshPosId (idSeq graph)
    let newgn = SCComponent{nodes = gnsNodes, getgnId = newId, iValue = newC}
        updatef f = \i -> updateEdge oldIdents newId $ f i
        updateSumm (f,k) = (updatef f, k)
        newSummaries v = V.map updateSumm v
    fuseDHT (nodeToGraphNode graph) gnsNodes newId newgn;
    updateEdges (edges graph) oldIdents newId;
    vt <- readSTRef (summaries graph)
    writeSTRef (summaries graph) $ newSummaries vt
    isA <- isAccepting graph newgn areFinal
    return (isA, Just $ (newId, oldIdents))

-- not safe
isAccepting :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> GraphNode state -> ([state] -> Bool) -> ST.ST s Bool
isAccepting graph gn areFinal = let gnStates SingleNode{node = n} = Set.singleton . getState . fst $ n
                                    gnStates SCComponent{nodes= ns} = Set.map (getState . fst) ns
                                    edgeGnIdents Internal{from=fr, to=t}          = Set.fromList [fr,t]
                                    edgeGnIdents Summary{from= fr, to=t, body =b} = Set.union (Set.fromList [fr,t]) $ Set.unions (Set.map edgeGnIdents b)
                                in do   
                                  gnEdges <- lookupEdges (edges graph) (getgnId gn) (getgnId gn)
                                  gnStatesList <- lookupApplyMultDHT (nodeToGraphNode graph) (Set.toList . Set.unions . Set.map edgeGnIdents $ gnEdges) gnStates
                                  let aF = debug (show gnStatesList) $ areFinal . Set.toList . Set.unions $ gnStatesList
                                  debug ("Found gn " ++ show gn ++ "with acceptance " ++ show aF ++ "\n") $ return aF


summariesSize :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s Int
summariesSize graph = do
    summ <- readSTRef $ summaries graph
    return $ V.length summ

-- here we don't want to remove the summaries
-- returns the new Initials
-- TODO: test this
toCollapsePhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (TwinSet Int)
toCollapsePhase graph = let unmarked list = snd . unzip $ filter (\(cond, _) -> cond) list
                            marked list = snd . unzip $ filter (\(cond, _) ->  not cond) list
                        in do 
                            modifyAllDHT (nodeToGraphNode graph) resetgnIValue
                            summ <- readSTRef $ summaries graph 
                            resolvedSummariesList <- forM (V.toList summ) $ resolveSummary graph
                            resetTS (initials graph); -- marks everything
                            return (Set.fromList $ unmarked resolvedSummariesList, Set.fromList $ marked resolvedSummariesList)


toSearchPhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> TwinSet Int -> ST.ST s ()
toSearchPhase graph ts = do 
  modifyAllDHT (nodeToGraphNode graph) resetgnIValue
  setTS (initials graph) ts;
  modifySTRef' (summaries graph) $ const (V.empty)

--unsafe
visitGraphFrom :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> (Maybe(Int, Set Int) -> ST.ST s ()) -> ([state] -> Bool) -> Key state -> ST.ST s Bool 
visitGraphFrom graph sbUpdater areFinal  key = do 
  gn <- lookupDHT (nodeToGraphNode graph) key 
  visitGraphFrom' graph sbUpdater areFinal gn 

visitGraphFrom' :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> (Maybe(Int, Set Int) -> ST.ST s ()) -> ([state] -> Bool) -> GraphNode state -> ST.ST s Bool 
visitGraphFrom' graph sbUpdater areFinal  gn = do 
  visitNode' graph gn;
  next <- nextStepsFrom (edges graph) (getgnId gn)
  nextGns <- lookupApplyMultDHT (nodeToGraphNode graph) (Set.toList next) id
  success <-  foldM (\acc gn -> if acc
                                  then return True 
                                  else if (iValue gn) == 0 
                                          then visitGraphFrom' graph sbUpdater areFinal gn
                                          else  do 
                                            updateSCC' graph (iValue gn)
                                            return False 
                                            )
                    False
                    nextGns 
  if success
    then return True 
    else  do 
      result <- createComponent' graph gn areFinal
      sbUpdater (snd result);
      return $ fst result











