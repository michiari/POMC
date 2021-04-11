{- |
   Module      : Pomc.SatUtils
   Copyright   : 2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.SatUtils ( SatState(..)
                     , Delta(..)
                     , StateId(..)
                     , Stack
                     , SIdGen
                     , SetMap
                     , TwinSet
                     , DoubleHashTable
                     , RecursiveTypes(..)
                     , debug
                     , initSIdGen
                     , wrapStates
                     , insertSM
                     , lookupSM
                     , memberSM
                     , emptySM
                     , emptyTS
                     , resetTS
                     , unmarkTS
                     , containsTS
                     , initializeTS
                     , setTS
                     , isMarkedTS
                     , valuesTS
                     , emptyDHT
                     , lookupIdDHT
                     , insertDHT
                     , multInsertDHT
                     , modifyDHT
                     , modifyAllDHT
                     , lookupDHT
                     , lookupApplyDHT
                     , getSidProps
                     ) where

import Pomc.Check ( EncPrecFunc)
import Pomc.State(Input, State(..))
import Pomc.Data (BitEncoding, extractInput)

import Control.Monad (foldM, forM_, forM, mapM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector)
import qualified Data.Vector as V


import Debug.Trace (trace)

class RecursiveTypes t where  
  subs :: t -> [Int]

debug :: String -> a -> a
debug _ x = x
--debug msg r = trace msg r 

type TwinSet a = (Set a, Set a)

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

initializeTS :: (Ord a, Show a) => STRef s (TwinSet a) -> Set a -> ST.ST s ()
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



-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v
type DoubleHashTable s k v = (HashTable s k Int, HashTable s Int v)

emptyDHT  :: v -> ST.ST s (DoubleHashTable s k v)
emptyDHT initialValue = do
  ht1 <- BH.new 
  ht2 <- BH.new
  return (ht1,ht2)

lookupIdDHT :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> ST.ST s (Maybe Int)
lookupIdDHT (ht1,_) key = BH.lookup ht1 key

-- insert a (key,value) tuple into the vht, with the given int identifier
insertDHT :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> Int -> v -> ST.ST s ()
insertDHT (ht1, ht2) key ident value = do 
  BH.insert ht1 key ident;
  BH.insert ht2 ident value
  

-- insert a set of keys into the vht, all mapped to the same value with the same identifier
multInsertDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Set k -> Int -> v -> ST.ST s ()
multInsertDHT (ht1, ht2) keySet ident value = do 
  forM_ (Set.toList keySet) ( \key -> BH.insert ht1 key ident);
  BH.insert ht2 ident value


-- not safe
lookupDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> k -> ST.ST s v
lookupDHT (ht1, ht2) key = do
  ident <- BH.lookup ht1 key
  value <- BH.lookup ht2 (fromJust ident)
  return $ fromJust value

-- True means is recursive
lookupApplyDHT :: (Eq k, Hashable k, RecursiveTypes v) => (DoubleHashTable s k v) -> Bool -> [Int] -> (v -> w) ->ST.ST s [w]
lookupApplyDHT (_,ht2) True idents f = recursiveLookupAndApplyDHT ht2 [] idents f 
lookupApplyDHT (_,ht2) False idents f = do 
  values <- forM idents $ BH.lookup ht2 
  return $ map (f . fromJust) values

recursiveLookupAndApplyDHT :: (RecursiveTypes v) => (HashTable s Int v) -> [w] -> [Int] -> (v -> w) ->ST.ST s [w]
recursiveLookupAndApplyDHT _ acc [] _ = return acc 
recursiveLookupAndApplyDHT ht acc idents f = do 
  values <- forM idents $ BH.lookup ht 
  let subidents = concatMap (subs . fromJust) values
      results   = map (f . fromJust) values 
  recursiveLookupAndApplyDHT ht (acc ++ results) subidents f 

--unsafe
modifyDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Int -> (v -> v) -> ST.ST s ()
modifyDHT (_, ht2) ident f = do 
  value <- BH.lookup ht2 ident 
  BH.insert ht2 ident $ f . fromJust $ value

modifyAllDHT :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> (v -> v) -> ST.ST s ()
modifyAllDHT (_, ht2) f = H.mapM_ (\(k,v) -> BH.insert ht2 k (f v)) ht2

-- Map to sets
type SetMap s v = MV.MVector s (Set v)


-- insert a state into the SetMap
insertSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s ()
insertSM smref stateid val = do
  sm <- readSTRef smref
  let len = MV.length sm
      sid = getId stateid
  if sid < len
    then MV.unsafeModify sm (Set.insert val) sid
    else let newLen = computeLen len sid

             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Set.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Set.insert val) sid
               ; writeSTRef smref grown
               }

lookupSM :: STRef s (SetMap s v) -> StateId state -> ST.ST s (Set v)
lookupSM smref stateid = do
  sm <- readSTRef smref
  let sid = getId stateid
  if sid < MV.length sm
    then MV.unsafeRead sm sid
    else return Set.empty

-- check whether a couple (StateId, Stack) iha already been visited checking the presence of the Stack in the Set at StateId position
memberSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s Bool
memberSM smref stateid val = do
  vset <- lookupSM smref stateid
  return $ val `Set.member` vset

-- an empty Set Map,  an array of sets
emptySM :: ST.ST s (STRef s (SetMap s v))
emptySM = do
  sm <- MV.replicate 4 Set.empty
  newSTRef sm


-- State class for satisfiability
class SatState state where
  getSatState ::  state -> State
  getStateProps :: BitEncoding -> state -> Input

instance SatState State where
  getSatState = id
  {-# INLINABLE getSatState #-}

  getStateProps bitencoding s = extractInput bitencoding (current $ s)
  {-# INLINABLE getStateProps #-}


-- States with unique IDs
data StateId state = StateId { getId :: !Int,
                               getState :: state } deriving (Show)

instance Eq (StateId state) where
  p == q = getId p == getId q

instance Ord (StateId state) where
  compare p q = compare (getId p) (getId q)

instance Hashable (StateId state) where
  hashWithSalt salt s = hashWithSalt salt $ getId s

-- a type to keep track of state to id relation
data SIdGen s state = SIdGen
  { idSequence :: STRef s Int -- a mutable variable in state thread s containing a variable of type Int
  , stateToId :: HashTable s state (StateId state) -- an HashTable where (key,value) = (state, StateId)
  }

initSIdGen :: ST.ST s (SIdGen s state)
initSIdGen = do
  newIdSequence <- newSTRef (1 :: Int) -- build a integer new STRef in the current state thread
  newStateToId <- H.new -- new empty HashTable
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

-- wrap a State into the StateId data type and into the ST monad, and update accordingly SidGen 
wrapState :: (Eq state, Hashable state)
          => SIdGen s state
          -> state
          -> ST.ST s (StateId state)
wrapState sig q = do
  qwrapped <- H.lookup (stateToId sig) q
  if isJust qwrapped
    then return $ fromJust qwrapped
    else do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    let newQwrapped = StateId newId q
    H.insert (stateToId sig) q newQwrapped
    return newQwrapped

--wrap a list of states into the ST monad, giving to each of them a unique ID
wrapStates :: (Eq state, Hashable state)
           => SIdGen s state -- keep track of state to id relation
           -> [state]
           -> ST.ST s (Vector (StateId state))
wrapStates sig states = do
  wrappedList <- V.mapM (wrapState sig) (V.fromList states)
  return wrappedList


-- Stack symbol: (input token, state) || Bottom if empty stack
type Stack state = Maybe (Input, StateId state) 


-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> Input -> [state] -- deltaPush relation
  , deltaShift :: state -> Input -> [state] -- deltaShift relation
  , deltaPop :: state -> state -> [state] -- deltapop relation
  }

-- get atomic propositions holding in a state
getSidProps :: (SatState state) => BitEncoding -> StateId state -> Input
getSidProps bitencoding s = (getStateProps bitencoding) . getState $ s