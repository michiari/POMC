{- |
   Module      : Pomc.DoubleHashtable
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
module Pomc.DoubleHashTable( DoubleHashTable
                           , empty
                           , lookupId
                           , insert
                           , fuse
                           , lookup
                           , lookupApply
                           , lookupMap
                           , modify
                           , modifyAll
                           ) where
import Prelude hiding (lookup)
import Control.Monad (forM_, forM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v
type DoubleHashTable s k v = (HashTable s k Int, HashTable s Int v)

empty  :: ST.ST s (DoubleHashTable s k v)
empty = do
  ht1 <- BH.new 
  ht2 <- BH.new
  return (ht1,ht2)

lookupId :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> ST.ST s (Maybe Int)
lookupId (ht1,_) key = BH.lookup ht1 key

-- insert a (key,value) tuple into the dht, with the given int identifier
insert :: (Eq k, Hashable k) => DoubleHashTable s k v -> k -> Int -> v -> ST.ST s ()
insert (ht1, ht2) key ident value = do 
  BH.insert ht1 key ident;
  BH.insert ht2 ident value
  

-- insert a set of keys into the dht, all mapped to the same value with the same identifier
fuse :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Set k -> Int -> v -> ST.ST s ()
fuse (ht1, ht2) keySet ident value = do 
  forM_ (Set.toList keySet) ( \key -> do 
                                        oldIdent <- BH.lookup ht1 key 
                                        BH.insert ht1 key ident;
                                        BH.delete ht2 $ fromJust oldIdent 
                            );
  BH.insert ht2 ident value


-- not safe
lookup :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> k -> ST.ST s v
lookup (ht1, ht2) key = do
  ident <- BH.lookup ht1 key
  value <- BH.lookup ht2 (fromJust ident)
  return $ fromJust value

-- not safe
lookupApply :: (Show v, Eq k, Hashable k) => (DoubleHashTable s k v) -> Int -> (v -> w) ->ST.ST s w
lookupApply (_,ht2) ident f = do 
    value <- BH.lookup ht2 ident        
    return $ f . fromJust $ value

-- not safe
lookupMap :: (Show v, Eq k, Hashable k) => (DoubleHashTable s k v) -> [Int] -> (v -> w) ->ST.ST s [w]
lookupMap (_,ht2) idents f =   do 
    values <- forM idents $ BH.lookup ht2         
    return $ map (f . fromJust) values

--unsafe
modify :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> Int -> (v -> v) -> ST.ST s ()
modify (_, ht2) ident f = do 
  value <- BH.lookup ht2 ident 
  BH.insert ht2 ident $ f . fromJust $ value

modifyAll :: (Eq k, Hashable k) => (DoubleHashTable s k v) -> (v -> v) -> ST.ST s ()
modifyAll (_, ht2) f = H.mapM_ (\(k,v) -> BH.insert ht2 k (f v)) ht2