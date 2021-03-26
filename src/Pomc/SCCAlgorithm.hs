{- |
   Module      : Pomc.SCC
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm () where
 -- TODO. optimize imports
import Pomc.Satisfiability( StateId(..), Stack, SatState) 
import qualified Data.Stack.ST  as StackST 

import Control.Monad ( forM_, forM) 
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef') 
import Data.Maybe 

import Data.Set (Set) 
import qualified Data.Set as Set 

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import GHC.Natural(naturalToInt)


import qualified Data.Vector.Mutable as MV 
import Data.Vector (Vector) 
import qualified Data.Vector as V 
import Data.List

data Edge k = Internal 
  { from :: k
  ,  to  :: k 
  } | Summary 
  { from :: k
  ,   to :: k
  ,  body :: Set (Edge k) 
  } deriving (Show, Ord)-- is it fine to derive Ord?

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
  }

instance (Ord k) => Eq (SummaryBody k) where 
  p == q = (firstNode p) == (firstNode q)
          && (lastNode p) == (lastNode q)
          && (all (\e -> Set.member e (bodyEdges q)) $ Set.toList (bodyEdges p))
          && (all (\e -> Set.member e (bodyEdges p)) $ Set.toList (bodyEdges q))
data GraphNode k state = SCComponent
  { getgnId   :: k -- immutable
  , iValue    :: Int -- changes at each iteration of the Gabow algorithm
  , nodes     :: Set (GraphNode k state)
  } | SingleNode
  { getgnId  :: k -- immutable
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
  } deriving (Show)

instance (Eq k) => Eq (GraphNode k state) where
  p == q = getgnId p == getgnId q

instance (Ord k) => Ord (GraphNode k state) where
  compare p q = compare (getgnId p) (getgnId q)

instance (Hashable k) => Hashable (GraphNode k state) where
  hashWithSalt salt s = hashWithSalt salt $ getgnId s

type HashTable s k v = BH.HashTable s k v
type DoubleHashTable s k v = (HashTable s k Int, HashTable s Int v)
type TwinSet a = (Set a, Set a)
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


-- TwinSet interface operation 
emptyTS :: ST.ST s (STRef s (TwinSet a))
emptyTS = newSTRef ((Set.empty, Set.empty))

resetTS :: (Ord a) => STRef s (TwinSet a) -> ST.ST s ()
resetTS tsref = modifySTRef' tsref  (\(s1,s2) -> (Set.empty, Set.union s1 s2)) 

unmarkTS :: (Ord a) => STRef s (TwinSet a) -> a -> ST.ST s ()
unmarkTS tsref val= modifySTRef' tsref (\(s1,s2) -> if Set.member val s2 
                                                      then (Set.insert val s1, Set.delete val s2)
                                                      else (s1,s2) 
                                        ) 

containsTS :: (Ord a) => STRef s (TwinSet a) -> a -> ST.ST s Bool
containsTS tsref val = do
  (s1,s2) <- readSTRef tsref
  return $ (Set.member val s1) || (Set.member val s2)

initializeTS :: (Ord a) => STRef s (TwinSet a) -> Set a -> ST.ST s ()
initializeTS tsref newSet = modifySTRef' tsref ( const (Set.empty, newSet)) 

setTS :: (Ord a) => STRef s (TwinSet a) -> TwinSet a -> ST.ST s ()
setTS tsref (s1,s2) = modifySTRef' tsref (const (s1,s2)) 

isMarkedTS :: (Ord a) => STRef s (TwinSet a) -> a -> ST.ST s Bool
isMarkedTS tsref val = do
  (s1,s2) <- readSTRef tsref
  return $ Set.member val s2

valuesTS :: (Ord a) => STRef s (TwinSet a) -> ST.ST s (Set a)
valuesTS tsref = do
  (s1,s2) <- readSTRef tsref
  return $ Set.union s1 s2 

----------------------------------------------------------------------------------------
emptyDHT  :: ST.ST s (DoubleHashTable s k v)
emptyDHT = do
            ht1 <- BH.new 
            ht2 <- BH.new
            return (ht1, ht2)

lookupIdDHT :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> ST.ST s (Maybe Int)
lookupIdDHT (ht1, _) key = BH.lookup ht1 key

-- insert a (key,value) tuple into the dht, with the given int identifier
insertDHT :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> Int -> v -> ST.ST s ()
insertDHT (ht1, ht2) key ident value = do 
  BH.insert ht1 key ident;
  BH.insert ht2 ident value

-- insert a set of keys into the dht, all mapped to the same value with the same identifier
multInsertDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Set k -> Int -> v -> ST.ST s ()
multInsertDHT (ht1, ht2) keySet ident value = do 
  forM_ (Set.toList keySet) ( \key -> BH.insert ht1 key ident);
  BH.insert ht2 ident value

deleteDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) ->  k -> ST.ST s ()
deleteDHT (ht1, ht2) key  = do 
  maybeId <- BH.lookup ht1 key
  BH.delete ht1 key;
  if (isJust maybeId)
    then BH.delete ht2 (fromJust maybeId)
    else return ()


multDeleteDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) ->  Set k -> ST.ST s ()
multDeleteDHT (ht1, ht2) keySet = forM_ (Set.toList keySet) ( \key -> deleteDHT (ht1,ht2) key)

-- not safe
lookupDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> k -> ST.ST s v
lookupDHT (ht1, ht2) key = do
  ident <- BH.lookup ht1 key
  value <- BH.lookup ht2 $ fromJust ident
  return $ fromJust value

-- not safe
lookupIntDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Int -> ST.ST s v
lookupIntDHT (_, ht2) ident = do
  value <- BH.lookup ht2 ident
  return $ fromJust value

insertIntDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Int -> v -> ST.ST s ()
insertIntDHT (_,ht2) ident val = BH.insert ht2 ident val  

keysDHT :: (Eq k, Hashable k, Ord k) => (DoubleHashTable s k v) -> ST.ST s (Set k)
keysDHT (ht1, _) = do 
  ht1entries <- H.toList ht1
  return $ Set.fromList $ fst . unzip $ ht1entries

valuesDHT :: (Eq k, Hashable k, Ord v) => (DoubleHashTable s k v) -> ST.ST s (Set v)
valuesDHT (_, ht2) = do 
  ht2entries <- H.toList ht2
  return $ Set.fromList . snd . unzip $ ht2entries

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

gnStates :: (SatState state, Eq state, Ord state, Hashable state, Show state)=> GraphNode k state-> Set state
gnStates (SingleNode{node = n}) = Set.singleton (getState . fst $ n)
gnStates (SCComponent{nodes = ns}) = Set.unions (Set.map gnStates ns)

-- get all the nodes (i.e, tuples (StateID state, Stack state)) which form a GraphNode
gnNodes :: (SatState state, Eq state, Hashable state, Show state) => GraphNode k state -> Set (Key state)
gnNodes (SingleNode{node = n}) = Set.singleton n
gnNodes (SCComponent{nodes = ns}) = Set.unions (Set.map gnNodes ns)  

containsStateId :: (SatState state, Eq state, Hashable state, Show state) =>  StateId state -> GraphNode k state -> Bool
containsStateId sid gn = let gnn = gnNodes gn 
                         in not $ Set.null $ Set.filter (\node -> fst node == sid) gnn -- TODO: maybe an alternative implementation performs better?

-- from a GraphNode, get a list of all recursive GraphNodes contained in it
flattengn :: (SatState state, Eq state, Hashable state, Show state, Ord k) => GraphNode k state -> Set (GraphNode k state)
flattengn n@(SingleNode{}) = Set.singleton n
flattengn n@(SCComponent{nodes = ns}) = Set.union (Set.singleton n) $ Set.unions (Set.map flattengn ns)
    
-- the iValue is used in the Gabow algorithm
setgnIValue ::  (SatState state, Eq state, Hashable state, Show state) => Int -> GraphNode k state -> GraphNode k state 
setgnIValue new (SCComponent { getgnId = gid, nodes = ns}) = SCComponent{ getgnId = gid, iValue = new,nodes = ns} 
setgnIValue new  SingleNode{getgnId = gid, node = n} = SingleNode{getgnId = gid, iValue = new, node = n}

resetgnIValue :: (SatState state, Eq state, Hashable state, Show state) => GraphNode k state -> GraphNode k state 
resetgnIValue  = setgnIValue 0

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
initialNodes :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (Vector (Key state))
initialNodes graph = do 
  inIdents <- valuesTS $ initials graph
  inGnList <- forM (Set.toList inIdents) (\ident -> lookupIntDHT (nodeToGraphNode graph) ident)
  return $ V.fromList $ Set.toList $ Set.unions $ map (gnNodes) inGnList


-- unsafe: precond: the node is already there
alreadyVisited :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s Bool 
alreadyVisited graph k = do
  graphNode <- lookupDHT (nodeToGraphNode graph) k
  return $ (iValue graphNode) == 0


-- True: the graphNode was already discovered, False otherwise
alreadyDiscovered :: (SatState state, Eq state, Hashable state, Show state) => Graph s state-> Key state-> ST.ST s Bool -- was the graphNode already there?
alreadyDiscovered graph key = do 
  ident <- lookupIdDHT (nodeToGraphNode graph) key
  if isJust ident
    then do 
          isMarked <- isMarkedTS (initials graph) $ fromJust ident
          return $ not isMarked 
    else do 
          ident <- freshPosId $ idSeq graph
          insertDHT (nodeToGraphNode graph) key ident SingleNode{getgnId = ident,iValue = 0, node = key };
          return False



-- unsafe
visitNode :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
visitNode graph key = do
  gn <- lookupDHT (nodeToGraphNode graph) key 
  unmarkTS (initials graph) $ getgnId gn;
  StackST.stackPush (sStack graph) (getgnId gn);
  sSize <- StackST.stackSize $ sStack graph 
  insertIntDHT (nodeToGraphNode graph) (getgnId gn) $ setgnIValue (naturalToInt sSize) gn;
  StackST.stackPush (bStack graph) (naturalToInt sSize);

--unsafe
updateSCC :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> ST.ST s ()
updateSCC graph node = do 
  gn <- lookupDHT (nodeToGraphNode graph) node
  topElemB <- StackST.stackPeek (bStack graph)
  if iValue gn < 0 || iValue gn >= (fromJust topElemB) -- TODO: shall we do some checks here about the fromJust?
    then return ()
    else do
      StackST.stackPop (bStack graph);
      updateSCC graph node


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
discoverSummaryBody :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> StateId state -> Key state  -> ST.ST s (SummaryBody Int)
discoverSummaryBody graph from to = let untilcond = \ident -> do 
                                                                gn <- lookupIntDHT (nodeToGraphNode graph) ident
                                                                return $ containsStateId from gn
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
insertInternal graph from to = do from <- lookupIdDHT (nodeToGraphNode graph) from
                                  to   <- lookupIdDHT (nodeToGraphNode graph) to
                                  modifySTRef' (edges graph) $ Set.insert $ Internal (fromJust from) (fromJust to)

-- unsafe
insertSummary :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> Key state -> Key state -> SummaryBody Int -> ST.ST s ()
insertSummary graph fromKey toKey  sb = do fr <- lookupIdDHT (nodeToGraphNode graph) fromKey
                                           t  <- lookupIdDHT (nodeToGraphNode graph) toKey
                                           modifySTRef' (edges graph) $ Set.insert $ buildSummary (fromJust fr) sb (fromJust t);
                                           modifySTRef' (edges graph) $ Set.insert $ Internal{from=(fromJust fr), to = firstNode sb};
                                           -- TODO: ricorda che qui non hai inserito l'edge lastNode - to


-- the same as CreateComponent in the algorithm
createComponent :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Key state -> ([state] -> Bool) -> ST.ST s Bool
createComponent graph key areFinal = do
  gn <- lookupDHT (nodeToGraphNode graph) key
  topB <- StackST.stackPeek (bStack graph) 
  if (isJust topB && (iValue gn) == (fromJust topB))
    then do 
      StackST.stackPop (bStack graph)
      createComponent' graph (iValue gn) Set.empty areFinal
    else return $ False 


createComponent' :: (SatState state, Ord state, Hashable state, Show state) => Graph s state -> Int -> Set Int -> ([state] -> Bool)  -> ST.ST s Bool
createComponent' graph iValue  acc areFinal = do
  sSize <- StackST.stackSize (sStack graph)
  if iValue < (naturalToInt sSize)
    then do 
      gnList <- forM (Set.toList acc) $ lookupIntDHT $ nodeToGraphNode graph
      unifyGns graph gnList areFinal
    else do
      elem <- StackST.stackPop (sStack graph)
      createComponent' graph iValue (Set.insert (fromJust elem) acc) areFinal
 
unifyGns :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> [GraphNode Int state]-> ([state] -> Bool) -> ST.ST s Bool
unifyGns graph [gn@(SCComponent{})] areFinal = return False
unifyGns graph [sn@(SingleNode{})]  areFinal = do
  self <- selfLoop (edges graph) (getgnId sn)
  if self 
    then do
      newC <- freshNegId (c graph)
      insertDHT (nodeToGraphNode graph) (node sn) (getgnId sn) (SCComponent{nodes = Set.singleton sn, getgnId = (getgnId sn), iValue = newC})
      isAccepting graph (SCComponent{nodes = Set.singleton sn, getgnId = (getgnId sn), iValue = newC}) areFinal
    else return False
unifyGns graph gns areFinal = do 
  multDeleteDHT (nodeToGraphNode graph) $ Set.unions $ map gnNodes gns;
  newC <- freshNegId (c graph)
  newId <- freshPosId (idSeq graph)
  multInsertDHT (nodeToGraphNode graph)  (Set.unions $ map gnNodes gns) newId $ SCComponent{nodes = Set.fromList gns, getgnId = newId, iValue = newC}
  isAccepting graph (SCComponent{nodes = Set.fromList gns, getgnId = newId, iValue = newC}) areFinal

-- not safe
isAccepting :: (SatState state, Ord state, Hashable state, Show state) => Graph s state  -> GraphNode Int state -> ([state] -> Bool) -> ST.ST s Bool
isAccepting graph gn areFinal = let gnList = Set.toList $ flattengn gn
                                    gnListIds = map getgnId gnList
                                    couples = [(from, to) | from <- gnListIds, to <- gnListIds] 
                                in do 
                                  edgeSetList <- forM couples (\(from,to) -> lookupEdge (edges graph) from to)
                                  gnList <- forM (Set.toList . Set.unions . Set.map edgeGNodes . Set.unions $ edgeSetList) $ lookupIntDHT $ nodeToGraphNode graph
                                  return $ areFinal (Set.toList . Set.unions . map gnStates $ gnList)


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
                            resetTS (initials graph);
                            return (Set.fromList $ unmarked resolvedSummariesList, Set.fromList $ marked resolvedSummariesList)


toSearchPhase :: (SatState state, Eq state, Hashable state, Show state) => Graph s state -> TwinSet Int -> ST.ST s ()
toSearchPhase graph ts = do 
  gns <- valuesDHT (nodeToGraphNode graph)
  forM_ (Set.toList gns) $ \gn -> insertIntDHT (nodeToGraphNode graph) (getgnId gn) (resetgnIValue gn);
  setTS (initials graph) ts;
  modifySTRef' (summaries graph) $ const (V.empty)

