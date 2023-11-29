{- |
   Module      : Pomc.MapMap
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.MapMap ( MapMap
                   , insert
                   , insertWith
                   , lookup
                   , member
                   , empty
                   , showMapMap
                   ) where

import Prelude hiding (lookup)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import qualified Data.Vector.Mutable as MV

import qualified Data.Map as Map
import Data.Map(Map)

-- Map to Maps
type MapMap s k v = MV.MVector s (Map k v)

-- insert a pair (key, value) into the MapMap
-- ensures: it replaces the existing mapping, if existing
insert :: (Ord k) => STRef s (MapMap s k v) -> Int -> k -> v -> ST.ST s ()
insert smref idx key val = do
  sm <- readSTRef smref
  let len = MV.length sm
  if idx < len
    then MV.unsafeModify sm (Map.insert key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Map.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Map.insert key val) idx
               ; writeSTRef smref grown
               }

-- insert a pair (key, value) into the MapMap
-- ensures: it uses the supplied combining function if the mapping is already present
insertWith :: (Ord k) => STRef s (MapMap s k v) -> Int -> (v -> v -> v) -> k -> v -> ST.ST s ()
insertWith smref idx f key val = do
  sm <- readSTRef smref
  let len = MV.length sm
  if idx < len
    then MV.unsafeModify sm (Map.insertWith f key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Map.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Map.insert key val) idx
               ; writeSTRef smref grown
               }

lookup :: STRef s (MapMap s k v) -> Int -> ST.ST s [(k,v)]
lookup smref idx = do
  sm <- readSTRef smref
  if idx < MV.length sm
    then Map.toList <$> MV.unsafeRead sm idx
    else return []

-- check the presence of the key in the Map at StateId position
member :: (Ord k) => STRef s (MapMap s k v) -> Int -> k -> ST.ST s Bool
member smref idx key = do
  sm <- readSTRef smref
  if idx < MV.length sm
    then Map.member key <$> MV.unsafeRead sm idx
    else return False

-- an empty Set Map, an array of sets
empty :: ST.ST s (STRef s (MapMap s k v))
empty = do
  sm <- MV.replicate 4 Map.empty
  newSTRef sm

-- for debugging purposes
showMapMap :: (Show  k, Show v) => MapMap s k v -> ST.ST s String
showMapMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Map at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""

