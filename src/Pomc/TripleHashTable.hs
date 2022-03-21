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
                           , merge
                           , lookup
                           , lookupApply
                           , lookupMap
                           , modify
                           , modifyAll
                           ) where

import Prelude hiding (lookup)
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
type TripleHashTable s v = (HashTable s (Int,Int,Int) Int, HashTable s Int Int, STRef s (MM.MaybeMap s v))

empty  :: ST s (TripleHashTable s v)
empty = do
  ht1 <- BH.new
  ht2 <- BH.new
  mm <- MM.empty
  return (ht1, ht2, mm)

lookupId :: TripleHashTable s v -> (Int,Int,Int) -> ST s (Maybe Int)
lookupId (ht1,_, _) key = BH.lookup ht1 key

insert :: TripleHashTable s v -> (Int,Int,Int) -> Int -> v -> ST s ()
insert (ht1, _, mm) key ident value = do
  BH.insert ht1 key ident;
  MM.insert mm ident value

merge :: (TripleHashTable s v) -> [(Int,Int,Int)] -> Int -> v -> ST s ()
merge (ht1, ht2, mm) keys ident value = do
  forM_ keys ( \key -> do
                        oldIdent <- BH.lookup ht1 key
                        BH.insert ht2 (fromJust oldIdent) ident
                        MM.delete mm $ fromJust oldIdent
              );
  MM.insert mm ident value

multcheckMerge :: HashTable s Int Int -> [Int] -> ST s (Set Int)
multcheckMerge ht is = 
  let maybeVal Nothing old  = old
      maybeVal (Just new) _ = new
  in foldM (\s ix -> do 
                      mi <- BH.lookup ht ix
                      return $ Set.insert (maybeVal mi ix) s)
            Set.empty
            is

checkMerge :: HashTable s Int Int -> Int -> ST s Int
checkMerge ht i = 
  let maybeVal Nothing old  = old
      maybeVal (Just new) _ = new
  in do
    mi <- BH.lookup ht i
    return $ maybeVal mi i

lookup :: (TripleHashTable s v) -> (Int,Int,Int) -> ST s v
lookup (ht1, ht2, mm) key = do
  ident <- BH.lookup ht1 key
  mergeIdent <- checkMerge ht2 (fromJust ident)
  value <- MM.lookup mm mergeIdent
  return $ fromJust value

lookupApply :: (TripleHashTable s v) -> Int -> (v -> w) -> ST s w
lookupApply (_, ht2, mm) ident f = do
  mergeIdent <- checkMerge ht2 ident
  value <- MM.lookup mm mergeIdent
  return $ f . fromJust $ value

lookupMap :: (TripleHashTable s  v) -> [Int] -> (v -> w) -> ST s [w]
lookupMap (_,ht2, mm) idents f =  do 
    mergeIdents <- multcheckMerge ht2 idents
    forM (Set.toList mergeIdents) $ \ident -> do
      value <- MM.lookup mm ident
      return $ f . fromJust $ value

modify :: (TripleHashTable s v) -> Int -> (v -> v) -> ST s ()
modify (_, ht2,mm) ident f = do 
  mergeIdent <- checkMerge ht2 ident
  MM.modify mm mergeIdent f

modifyAll :: (TripleHashTable s  v) -> (v -> v) -> ST s ()
modifyAll (_, _,  mm) f = MM.modifyAll mm f
