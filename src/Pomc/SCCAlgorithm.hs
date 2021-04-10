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
                         , newSummariesSize
                         , toCollapsePhase
                         , toSearchPhase
                         , visitNode
                         , createComponent
                         , discoverSummaryBody
                         , insertInternal
                         , insertSummary
                         , discoverSummary
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
import Data.List

import Data.Hashable

data Edge k = Internal 
  { from :: k
  ,  to  :: k 
  } | Summary 
  { from :: k
  ,   to :: k
  ,  body :: Set (Edge k) 
  } deriving (Show, Ord)

instance (Ord k) => Eq (Edge k) where
  p@(Internal{}) == q@(Internal{}) = (from p) == (from q) && (to p) == (to q) 
  p@(Summary{})  == q@(Summary{}) = (from p) == (from q) 
                                    && (to p) == (to q)
                                    && (all (\e -> Set.member e (body q)) $ Set.toList (body p))
                                    && (all (\e -> Set.member e (body p)) $ Set.toList (body q))
  _ == _ = False

-- the nodes which form a  summary body
data SummaryBody k = SummaryBody 
  { firstNode :: k
  , lastNode  :: k 
  , bodyEdges :: Set (Edge k)
  } deriving (Show,Ord)

instance (Ord k) => Eq (SummaryBody k) where 
  p == q = (firstNode p) == (firstNode q)
          && (lastNode p) == (lastNode q)
          && (all (\e -> Set.member e (bodyEdges q)) $ Set.toList (bodyEdges p))
          && (all (\e -> Set.member e (bodyEdges p)) $ Set.toList (bodyEdges q))

data GraphNode k state = SCComponent
  { getgnId   :: k -- immutable
  , iValue    :: Int -- changes at each iteration of the Gabow algorithm
  , nodes     :: Set Int
  } | SingleNode
  { getgnId  :: k -- immutable
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
  } 

instance (Show k, Show state) => Show (GraphNode k state) where
  show gn@SingleNode{} =  show $ getgnId gn 
  show gn@SCComponent{} = (show $ getgnId gn) ++ "components: " ++ (concatMap (\gn -> show gn ++ ",") $ nodes gn ) ++ "\n"


instance (Eq k) => Eq (GraphNode k state) where
  p == q = getgnId p == getgnId q

instance (Ord k) => Ord (GraphNode k state) where
  compare p q = compare (getgnId p) (getgnId q)

instance (Hashable k) => Hashable (GraphNode k state) where
  hashWithSalt salt s = hashWithSalt salt $ getgnId s

type Key state = (StateId state, Stack state)
type Value k state = GraphNode k state
type GabowStack s v = StackST.Stack s v

-- this is not parametrized
data Graph s state = Graph
  { idSeq           :: STRef s Int
  , nodeToGraphNode :: DoubleHashTable s (Key state) (Value Int state)
  , edges           :: STRef s (Set (Edge Int)) -- Set is not keyed in the monad, it needs a STRef
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GabowStack s Int -- for the Gabow algorithm
  , sStack          :: GabowStack s Int -- for the Gabow algorithm
  , initials        :: STRef s (TwinSet Int)
  , summaries       :: STRef s (Vector (Int -> Edge Int, Key state))
  }


----------------------------------------------------------------------------------------

-- TODO: update this to reuse the code of gnNodes
gnStates :: (SatState state, Eq state, Ord state, Hashable state, Show state)=> Graph s state -> GraphNode k state-> ST.ST s (Set state)
gnStates _        (SingleNode{node = n}) = return $ Set.singleton (getState . fst $ n)
gnStates graph (SCComponent{nodes = ns}) = do 
  gns <- forM (Set.toList ns) $ lookupIntDHT (nodeToGraphNode graph)
  stateSetList <- forM gns $ gnStates graph
  return $ Set.unions stateSetList

-- get all the nodes (i.e, tuples (StateID state, Stack state)) which form a GraphNode
gnNodes :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> GraphNode Int state -> ST.ST s (Set (Key state))
gnNodes _        (SingleNode{node = n}) = return $ Set.singleton n
gnNodes graph (SCComponent{nodes = ns}) = do 
  gns <- forM (Set.toList ns) $ lookupIntDHT (nodeToGraphNode graph)
  nodeSetList <- forM (gns) $ gnNodes graph
  return $ Set.unions nodeSetList  

containsStateId :: (SatState state, Eq state, Hashable state, Show state) =>  Graph s state -> StateId state -> GraphNode Int state -> ST.ST s Bool
containsStateId graph sid gn = do 
  nodes <- gnNodes graph gn 
  return $  not $ Set.null $ Set.filter (\node -> fst node == sid) nodes 

-- from a GraphNode, get a list of all recursive GraphNodes contained in it
flattengn :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> GraphNode Int state -> ST.ST s (Set Int)
flattengn _     n@(SingleNode{}) = return $ Set.singleton $ getgnId n
flattengn graph n@(SCComponent{nodes = ns}) = do
  gns <- forM (Set.toList ns) $ lookupIntDHT (nodeToGraphNode graph)
  identSetList <- forM gns $ flattengn graph 
  return $ Set.union (Set.singleton $ getgnId n) $ Set.unions identSetList
    
-- the iValue is used in the Gabow algorithm
setgnIValue ::  (SatState state, Eq state, Hashable state, Show state) => Int -> GraphNode k state -> GraphNode k state 
setgnIValue new (SCComponent { getgnId = gid, nodes = ns}) = SCComponent{ getgnId = gid, iValue = new,nodes = ns} 
setgnIValue new  SingleNode{getgnId = gid, node = n} = SingleNode{getgnId = gid, iValue = new, node = n}

resetgnIValue :: (SatState state, Eq state, Hashable state, Show state) => GraphNode k state -> GraphNode k state 
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

lookupEdge :: (Ord k) => STRef s (Set (Edge k)) -> k -> k -> ST.ST s (Set (Edge k))
lookupEdge edgeref fr t = do
  edgeSet <- readSTRef edgeref
  return $ Set.fromList $ filter (\e -> from e == fr && to e == t) $ Set.toList edgeSet -- can we have an Internal and a Summary with the same from and to?

edgeGNodes :: (Ord k) => Edge k -> Set k
edgeGNodes (Internal{from=fr, to=t}) = Set.fromList [fr,t]
edgeGNodes (Summary{from= fr, to=t, body =b}) = Set.union (Set.fromList [fr,t]) $ Set.unions (Set.map edgeGNodes b)

selfLoop :: (Ord k ) => STRef s (Set (Edge k)) -> k -> ST.ST s Bool
selfLoop edgeref node = do
  selfEdges <- lookupEdge edgeref node node 
  return $ not $ Set.null selfEdges 

-- this is used in let it run
nextStepsFrom :: (Ord k) => STRef s (Set (Edge k)) -> k -> ST.ST s (Set  k)
nextStepsFrom edgeref fr  = do
  edgeSet <- readSTRef edgeref
  return $ Set.fromList $ map (\e -> to e) $ filter (\e -> from e == fr) $ Set.toList edgeSet

-- map a list of nodes to the set of edges which connect them
toEdges :: (Ord k) => STRef s (Set (Edge k)) -> Set (Edge k) -> [k] -> ST.ST s (Set (Edge k))
toEdges edgeref acc [x] = return acc
toEdges edgeref acc (x:y:xs) = do 
                                found <- lookupEdge edgeref x y 
                                toEdges edgeref  (Set.union acc found) (y:xs)

buildSummary :: (Ord k) => k -> SummaryBody k -> k -> Edge k
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
  newIdSequence <- newSTRef (1 :: Int)
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
initialNodes bitenc graph = do 
  inIdents <- valuesTS $ initials graph
  inGnList <- forM (Set.toList inIdents) (\ident -> lookupIntDHT (nodeToGraphNode graph) ident)
  gnNodesList <- forM inGnList $ gnNodes graph
  let results =  Set.toList $ Set.unions $ gnNodesList
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
  debug ("Visiting node: " ++ show gn) $ visitNode' graph gn
  

visitNode' :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> GraphNode Int state -> ST.ST s ()
visitNode' graph gn = do 
  unmarkTS (initials graph) $ getgnId gn;
  StackST.stackPush (sStack graph) (getgnId gn);
  sSize <- StackST.stackSize $ sStack graph 
  insertIntDHT (nodeToGraphNode graph) (getgnId gn) $ setgnIValue (naturalToInt sSize) gn;
  StackST.stackPush (bStack graph) (naturalToInt sSize)

--unsafe
updateSCC :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
updateSCC graph key = do 
  gn <- lookupDHT (nodeToGraphNode graph) key
  updateSCC' graph (iValue gn) 

updateSCC' :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Int -> ST.ST s ()
updateSCC' graph iValue =  do 
  return ();
  topElemB <- StackST.stackPeek (bStack graph)
  if (iValue  < 0) || (iValue  >= (fromJust topElemB)) -- TODO: shall we do some checks here about the fromJust?
    then debug ("Cannot find other nodes to merge\n") $ return ()
    else do
      StackST.stackPop (bStack graph);
      updateSCC' graph iValue



-- when this is called, the current initials have nothing marked!!
-- safe
resolveSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Int -> Edge Int, Key state) -> ST.ST s (Bool, Int)
resolveSummary graph (builder, key) = do 
  alrDir <- alreadyDiscovered graph key 
  ident <- lookupIdDHT (nodeToGraphNode graph) key
  modifySTRef' (edges graph) $ Set.insert $ builder $ fromJust ident;
  return (alrDir, fromJust ident)

-- this simply creates a Summary Body
-- unsafe
discoverSummaryBody :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> StateId state -> ST.ST s (SummaryBody Int)
discoverSummaryBody graph from    = let untilcond = \ident -> do 
                                                                gn <- lookupIntDHT (nodeToGraphNode graph) ident
                                                                cont <- containsStateId graph from gn
                                                                return cont
                                    in do  
                                        body <- allUntil (sStack graph) [] untilcond
                                        edgeSet <- toEdges (edges graph) Set.empty body 
                                        return $ SummaryBody{firstNode = head body, lastNode = last body, bodyEdges = edgeSet}

-- unsafe 
discoverSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> SummaryBody Int ->  Key state -> ST.ST s ()
discoverSummary graph from body to = do 
  gnFrom <- lookupDHT (nodeToGraphNode graph) from 
  modifySTRef' (summaries graph) $ V.cons (\toInt -> buildSummary (getgnId gnFrom) body toInt, to)

-- unsafe
insertInternal :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> ST.ST s ()
insertInternal graph fromKey toKey  = do from <- lookupIdDHT (nodeToGraphNode graph) fromKey
                                         to   <- lookupIdDHT (nodeToGraphNode graph) toKey
                                         debug ("InsertInternal: from: " ++ show from ++ "} ---> to: " ++ show to ++ "\n") $ modifySTRef' (edges graph) $ Set.insert $ Internal (fromJust from) (fromJust to)

-- unsafe
insertSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> SummaryBody Int -> ST.ST s ()
insertSummary graph fromKey toKey  sb = do fr <- lookupIdDHT (nodeToGraphNode graph) fromKey
                                           t  <- lookupIdDHT (nodeToGraphNode graph) toKey
                                           let summ =  buildSummary (fromJust fr) sb (fromJust t)
                                           modifySTRef' (edges graph) $ Set.insert summ
                                           debug  ("InsertSummary: from: " ++ show fr ++ "} ---> to: " ++ show t ++ "edge: " ++ show summ ++ "\n") $ modifySTRef' (edges graph) $ Set.insert $ Internal{from=(fromJust fr), to = firstNode sb};
                                           -- TODO: ricorda che qui non hai inserito l'edge lastNode - to


-- the same as CreateComponent in the algorithm
-- TODO: update these functions' names to make the code more readable
createComponent :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Key state -> ([state] -> Bool) -> ST.ST s Bool
createComponent graph key areFinal = do
  gn <- lookupDHT (nodeToGraphNode graph) key
  debug ("creating component for node: " ++ show gn) $ createComponent' graph gn areFinal

createComponent' :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> GraphNode Int state -> ([state] -> Bool) -> ST.ST s Bool
createComponent' graph gn areFinal = do
  topB <- StackST.stackPeek (bStack graph) 
  if  (iValue gn) == (fromJust topB)
    then do 
      StackST.stackPop (bStack graph)
      mergeComponents graph (iValue gn) Set.empty areFinal
    else return $ False 




mergeComponents :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Int -> Set Int -> ([state] -> Bool)  -> ST.ST s Bool
mergeComponents graph iValue  acc areFinal = do
  sSize <- StackST.stackSize (sStack graph)
  if iValue > (naturalToInt sSize)
    then do 
      gnList <- forM (Set.toList acc) $ lookupIntDHT $ nodeToGraphNode graph
      unifyGns graph gnList areFinal
    else do
      elem <- StackST.stackPop (sStack graph)
      mergeComponents graph iValue (Set.insert (fromJust elem) acc) areFinal
 
-- TODO: update this to optimize the case when we have a single SCComponent
unifyGns :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> [GraphNode Int state]-> ([state] -> Bool) -> ST.ST s Bool
unifyGns graph [gn@(SingleNode{})]  areFinal = do
  newC <- freshNegId (c graph)
  insertDHT (nodeToGraphNode graph) (node gn) (getgnId gn) $ setgnIValue newC gn
  self <- selfLoop (edges graph) (getgnId gn)
  if self 
    then debug ("Single Node with Cycle found: " ++ show (setgnIValue newC gn) ++ "\n") $ isAccepting graph gn areFinal
    else debug ("Single Node without Cycle found: " ++ show (setgnIValue newC gn) ++ "\n") $ return False
unifyGns graph gns areFinal = do 
  newC <- freshNegId (c graph)
  newId <- freshPosId (idSeq graph)
  let newgn = SCComponent{nodes = Set.fromList . map getgnId $ gns, getgnId = newId, iValue = newC}
  gnNodesList <- forM gns $ gnNodes graph
  multInsertDHT (nodeToGraphNode graph)  (Set.unions gnNodesList) newId newgn 
  isAccepting graph   (debug ("SCComponent found: " ++ "\n") newgn) areFinal

-- not safe
isAccepting :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> GraphNode Int state -> ([state] -> Bool) -> ST.ST s Bool
isAccepting graph gn areFinal = let couples list = [(from, to) | from <- list, to <- list] 
                                in do 
                                  ids <- flattengn graph gn 
                                  edgeSetList <- forM (couples . Set.toList $ ids) (\(from,to) -> lookupEdge (edges graph) from to)
                                  gnList <- forM (Set.toList . Set.unions . Set.map edgeGNodes . Set.unions $ edgeSetList) $ lookupIntDHT $ nodeToGraphNode graph
                                  gnStatesList <- forM gnList $ \n ->  do states <- gnStates graph n 
                                                                          return (n,states)
                                  let aF = debug (show gnStatesList) $ areFinal (Set.toList . Set.unions . snd . unzip $ gnStatesList)
                                  debug ("Found gn " ++ show gn ++ "with acceptance " ++ show aF ++ "\n") $ return aF


newSummariesSize :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s Int
newSummariesSize graph = do
    summ <- readSTRef $ summaries graph
    return $ V.length summ

-- here we don't want to remove the summaries
-- returns the new Initials
-- TODO: test this
toCollapsePhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (TwinSet Int)
toCollapsePhase graph = let unmarked list = snd . unzip $ filter (\(cond, _) -> cond) list
                            marked list = snd . unzip $ filter (\(cond, _) ->  not cond) list
                        in do 
                            gns <- valuesDHT (nodeToGraphNode graph)
                            forM_ (Set.toList gns) $ \gn -> insertIntDHT (nodeToGraphNode graph) (getgnId gn) (resetgnIValue gn);
                            summ <- readSTRef $ summaries graph 
                            resolvedSummariesList <- forM (V.toList summ) $ resolveSummary graph
                            resetTS (initials graph); -- marks everything
                            return (Set.fromList $ unmarked resolvedSummariesList, Set.fromList $ marked resolvedSummariesList)


toSearchPhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> TwinSet Int -> ST.ST s ()
toSearchPhase graph ts = do 
  gns <- valuesDHT (nodeToGraphNode graph)
  forM_ (Set.toList gns) $ \gn -> insertIntDHT (nodeToGraphNode graph) (getgnId gn) (resetgnIValue gn);
  setTS (initials graph) ts;
  modifySTRef' (summaries graph) $ const (V.empty)

--unsafe
visitGraphFrom :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> ([state] -> Bool) -> Key state -> ST.ST s Bool 
visitGraphFrom graph areFinal key = do 
  gn <- lookupDHT (nodeToGraphNode graph) key 
  debug ("Calling visitNode from node: " ++ show gn) $ visitGraphFrom' graph areFinal gn 

visitGraphFrom' :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> ([state] -> Bool) -> GraphNode Int state -> ST.ST s Bool 
visitGraphFrom' graph areFinal gn = do 
  visitNode' graph gn;
  next <- nextStepsFrom (edges graph) (getgnId gn)
  nextNodes <- mapM (\n -> lookupIntDHT (nodeToGraphNode graph) n) $ Set.toList next
  success <-  foldM (\acc gn -> if acc
                                  then return True 
                                  else if (iValue gn) == 0 
                                          then visitGraphFrom' graph areFinal gn
                                          else  do 
                                            updateSCC' graph (iValue gn)
                                            return False 
                                            )
                    False
                    nextNodes 
  if success
    then return True 
    else createComponent' graph gn areFinal









