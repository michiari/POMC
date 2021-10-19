{- |
   Module      : Pomc.TripleHashtable
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.TripleHashTable( TripleHashTable
                           , empty
                           , lookupId
                           , insert
                           , fuse
                           , lookup
                           , lookupApply
                           , lookupMap
                           , modify
                           , multModify
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

import qualified Pomc.MaybeMap as MM

import Control.DeepSeq(NFData(..), deepseq)
import Data.STRef (STRef)

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v
type TripleHashTable s v = (HashTable s (Int,Int,Int) Int, STRef s (MM.MaybeMap s v))

empty  :: ST.ST s (TripleHashTable s v)
empty = do
  ht <- BH.new
  mm <- MM.empty
  return (ht,mm)

lookupId :: TripleHashTable s v -> (Int,Int,Int) -> ST.ST s (Maybe Int)
lookupId (ht,_) key = BH.lookup ht key

-- insert a (key,value) tuple into the dht, with the given int identifier
insert :: TripleHashTable s v -> (Int,Int,Int) -> Int -> v -> ST.ST s ()
insert (ht, mm) key ident value = do
  BH.insert ht key ident;
  MM.insert mm ident value


-- insert a set of keys into the dht, all mapped to the same value with the same identifier
fuse :: (TripleHashTable s v) -> Set (Int,Int,Int) -> Int -> v -> ST.ST s ()
fuse (ht, mm) keySet ident value = do
  forM_ (Set.toList keySet) ( \key -> do
                                oldIdent <- BH.lookup ht key
                                BH.insert ht key ident;
                                MM.delete mm $ fromJust oldIdent
                            );
  MM.insert mm ident value

-- not safe
lookup :: (TripleHashTable s v) -> (Int,Int,Int) -> ST.ST s v
lookup (ht, mm) key = do
  ident <- BH.lookup ht key
  value <- MM.lookup mm (fromJust ident)
  return $ fromJust value

-- not safe
lookupApply :: (TripleHashTable s v) -> Int -> (v -> w) -> ST.ST s w
lookupApply (_,mm) ident f = do
  value <- MM.lookup mm ident
  return $ f . fromJust $ value

-- not safe
lookupMap :: (TripleHashTable s  v) -> [Int] -> (v -> w) -> ST.ST s [w]
lookupMap (_,mm) idents f =  forM idents $ \ident -> do
  value <- MM.lookup mm ident
  return $ f . fromJust $ value

modify :: (TripleHashTable s v) -> Int -> (v -> v) -> ST.ST s ()
modify (_, mm) ident f = MM.modify mm ident f

multModify :: (TripleHashTable s v) -> [Int] -> (v -> v) -> ST.ST s ()
multModify (_,mm) idents f = MM.multModify mm idents f

modifyAll :: (TripleHashTable s  v) -> (v -> v) -> ST.ST s ()
modifyAll (_, mm) f = MM.modifyAll mm f
