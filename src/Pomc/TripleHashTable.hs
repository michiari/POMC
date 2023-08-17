{- |
   Module      : Pomc.TripleHashtable
   Copyright   : 2021-2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.TripleHashTable( TripleHashTable
                           , empty
                           , lookupId
                           , insert
                           , merge
                           , lookup
                           , unsafeLookup
                           , apply
                           , unsafeApply
                           , map
                           , unsafeMap
                           , modify
                           , unsafeModify
                           , modifyAll
                           ) where

import Prelude hiding (lookup, map)
import Control.Monad (forM_, forM, foldM)
import Control.Monad.ST (ST)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashTable.ST.Basic as BH
import Data.STRef (STRef)

import qualified Pomc.MaybeMap as MM

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- an hashtable indexed by three-ints-tuples
-- needed in the SCC algorithm.
type TripleHashTable s v = (HashTable s (Int,Int,Int) Int, HashTable s Int Int, STRef s (MM.MaybeMap s v))

-- internal functions
multCheckMerge :: HashTable s Int Int -> [Int] -> ST s (Set Int)
multCheckMerge ht is = 
  let maybeVal Nothing old  = old
      maybeVal (Just new) _ = new
  in foldM (\s ix -> do 
                      mi <- BH.lookup ht ix
                      return $ Set.insert (maybeVal mi ix) s)
            Set.empty
            is

checkMerge :: HashTable s Int Int -> Int -> ST s Int
checkMerge ht i = 
  let maybeVal Nothing    = i
      maybeVal (Just new) = new
  in do
    mi <- BH.lookup ht i
    return $ maybeVal mi
-- end internal functions

empty  :: ST s (TripleHashTable s v)
empty = do
  ht1 <- BH.new
  ht2 <- BH.new
  mm <- MM.empty
  return (ht1, ht2, mm)

lookupId :: TripleHashTable s v -> (Int,Int,Int) -> ST s (Maybe Int)
lookupId (ht1,_, _) = BH.lookup ht1

insert :: TripleHashTable s v -> (Int,Int,Int) -> Int -> v -> ST s ()
insert (ht1, _, mm) key ident value = do
  BH.insert ht1 key ident
  MM.insert mm ident value

merge :: TripleHashTable s v -> [(Int,Int,Int)] -> Int -> v -> ST s ()
merge (ht1, ht2, mm) keys ident value = do
  forM_ keys ( \key -> do
                        oldIdent <- BH.lookup ht1 key
                        BH.insert ht2 (fromJust oldIdent) ident
                        MM.delete mm $ fromJust oldIdent
              )
  MM.insert mm ident value

lookup :: TripleHashTable s v -> (Int,Int,Int) -> ST s v
lookup (ht1, ht2, mm) key = do
  ident <- BH.lookup ht1 key
  mergeIdent <- checkMerge ht2 (fromJust ident)
  value <- MM.lookup mm mergeIdent
  return $ fromJust value

unsafeLookup :: TripleHashTable s v -> (Int,Int,Int) -> ST s v
unsafeLookup (ht1, _, mm) key = do
  ident <- BH.lookup ht1 key
  value <- MM.lookup mm (fromJust ident)
  return $ fromJust value

apply :: TripleHashTable s v -> Int -> (v -> w) -> ST s w
apply (_, ht2, mm) ident f = do
  mergeIdent <- checkMerge ht2 ident
  value <- MM.lookup mm mergeIdent
  return $ f . fromJust $ value

unsafeApply :: TripleHashTable s v -> Int -> (v -> w) -> ST s w
unsafeApply (_, _, mm) ident f = do
  value <- MM.lookup mm ident
  return $ f . fromJust $ value

map :: TripleHashTable s  v -> [Int] -> (v -> w) -> ST s [w]
map (_,ht2, mm) idents f =  do 
    mergeIdents <- multCheckMerge ht2 idents
    forM (Set.toList mergeIdents) $ \ident -> do
      value <- MM.lookup mm ident
      return $ f . fromJust $ value

unsafeMap :: TripleHashTable s  v -> [Int] -> (v -> w) -> ST s [w]
unsafeMap (_, _, mm) idents f =  do 
    forM idents $ \ident -> do
      value <- MM.lookup mm ident
      return $ f . fromJust $ value

modify :: TripleHashTable s v -> Int -> (v -> v) -> ST s ()
modify (_, ht2, mm) ident f = do 
  mergeIdent <- checkMerge ht2 ident
  MM.modify mm mergeIdent f

unsafeModify :: TripleHashTable s v -> Int -> (v -> v) -> ST s ()
unsafeModify (_, _, mm) = MM.modify mm

modifyAll :: TripleHashTable s v -> (v -> v) -> ST s ()
modifyAll (_, _,  mm) = MM.modifyAll mm
