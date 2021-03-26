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

instance (Eq k, Ord k) => Eq (Edge k) where
  p@(Internal{}) == q@(Internal{}) = (from p) == (from q) && (to p) == (to q) 
  p@(Summary{})  == q@(Summary{}) = (from p) ==( from q) 
                                    && (to p) == (to q )
                                    && (all (\e -> Set.member e (body q)) $ Set.toList (body p))
                                    && (all (\e -> Set.member e (body p)) $ Set.toList (body q))
  _ == _ = False

-- the nodes which form a  summary body
data SummaryBody k = SummaryBody 
  { firstNode :: k
  , lastNode  :: k 
  , bodyEdges :: Set (Edge k)
  }

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
  , summaries       :: STRef s (Set (Int -> Edge Int, Key state))
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

newGraph :: (SatState state, Eq state, Hashable state, Show state) => Vector (Key state) -> ST.ST s (Graph s state)
newGraph initials = do
  newIdSequence <- newSTRef (1 :: Int)
  dht           <- emptyDHT
  newSet        <- newSTRef (Set.empty)
  newCSequence  <- newSTRef (-1 :: Int)
  newBS         <- StackST.stackNew
  newSS         <- StackST.stackNew
  newInitials   <- emptyTS
  newSummaries  <- newSTRef(Set.empty)
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
