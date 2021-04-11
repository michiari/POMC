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
                     , VectorHashTable
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
                     , emptyVHT
                     , lookupIdVHT
                     , insertVHT
                     , multInsertVHT
                     , modifyVHT
                     , modifyMultVHT
                     , modifyAllVHT
                     , lookupVHT
                     , lookupApplyVHT
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
type VectorHashTable s k v = (HashTable s k Int, STRef s (MV.MVector s v), v)

emptyVHT  :: v -> ST.ST s (VectorHashTable s k v)
emptyVHT initialValue = do
  ht <- BH.new 
  vt <- MV.replicate 4 initialValue
  vtref <- newSTRef vt
  return (ht, vtref,initialValue)

lookupIdVHT :: (Eq k, Hashable k) => VectorHashTable s k v -> k -> ST.ST s (Maybe Int)
lookupIdVHT (ht, _, _) key = BH.lookup ht key

-- insert a (key,value) tuple into the vht, with the given int identifier
insertVHT :: (Eq k, Hashable k) => VectorHashTable s k v -> k -> Int -> v -> ST.ST s ()
insertVHT (ht, vtref, ini) key ident value = do 
  BH.insert ht key ident;
  insertVT vtref ident value ini
  

-- insert a set of keys into the vht, all mapped to the same value with the same identifier
multInsertVHT :: (Eq k, Hashable k) => (VectorHashTable s k v) -> Set k -> Int -> v -> ST.ST s ()
multInsertVHT (ht, vtref, ini) keySet ident value = do 
  forM_ (Set.toList keySet) ( \key -> BH.insert ht key ident);
  insertVT vtref ident value ini


insertVT :: STRef s (MV.MVector s v) -> Int -> v -> v ->  ST.ST s ()
insertVT vtref ident value ini = do
  vt <- readSTRef vtref
  let len = MV.length vt
  if ident < len
    then MV.unsafeWrite vt ident value
    else let newLen = computeLen len ident
             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow vt (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i ini) [len..(newLen-1)]
               ; MV.unsafeWrite grown ident value
               ; writeSTRef vtref grown
               }

-- not safe
lookupVHT :: (Eq k, Hashable k) => (VectorHashTable s k v) -> k -> ST.ST s v
lookupVHT (ht1, vtref, _) key = do
  ident <- BH.lookup ht1 key
  vt <- readSTRef vtref
  MV.unsafeRead vt $ fromJust ident


-- True means is recursive
lookupApplyVHT :: (Eq k, Hashable k, RecursiveTypes v) => (VectorHashTable s k v) -> Bool -> [Int] -> (v -> w) ->ST.ST s [w]
lookupApplyVHT (_,vtref,_) True idents f = do 
  vt <- readSTRef vtref 
  recursiveLookupAndApplyVHT vt [] idents f 
lookupApplyVHT (_,vtref,_) False idents f = do 
  vt <- readSTRef vtref 
  values <- forM idents $ MV.unsafeRead vt 
  return $ map f values

recursiveLookupAndApplyVHT :: (RecursiveTypes v) => (MV.MVector s v) -> [w] -> [Int] -> (v -> w) ->ST.ST s [w]
recursiveLookupAndApplyVHT _ acc [] _ = return acc 
recursiveLookupAndApplyVHT vt acc idents f = do 
  values <- forM idents $ MV.unsafeRead vt 
  let subidents = concatMap (subs) values
      results   = map f values 
  recursiveLookupAndApplyVHT vt (acc ++ results) subidents f 

modifyVHT :: (Eq k, Hashable k) => (VectorHashTable s k v) -> Int -> (v -> v) -> ST.ST s ()
modifyVHT (_, vtref, _) ident f = do
  vt <- readSTRef vtref 
  MV.unsafeModify vt f ident

modifyMultVHT :: (Eq k, Hashable k) => (VectorHashTable s k v) -> (v -> v) -> [Int] -> ST.ST s ()
modifyMultVHT (_, vtref, _) f idents = do
  vt <- readSTRef vtref 
  forM_ idents $ MV.unsafeModify vt f 

modifyAllVHT :: (Eq k, Hashable k) => (VectorHashTable s k v) -> (v -> v) -> ST.ST s ()
modifyAllVHT (_, vtref, _) f = do 
  vt <- readSTRef vtref 
  forM_ [0..((MV.length vt) -1)] $ MV.unsafeModify vt f



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