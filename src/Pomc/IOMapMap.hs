{- |
   Module      : Pomc.IOIOMapMap
   Copyright   : 2024 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.IOMapMap ( IOMapMap
                   , insert
                   , insertWith
                   , lookup
                   , lookupValue
                   , member
                   , delete
                   , empty
                   , showIOMapMap
                   , foldMaps
                   ) where

import Prelude hiding (lookup)

import qualified Data.Vector.Mutable as MV

import qualified Data.Map as Map
import Data.Map(Map)
import Data.IORef (readIORef, IORef, newIORef, writeIORef)
import Data.Vector.Mutable (IOVector)

import Control.Monad(when)

-- Map to Maps
type IOMapMap k v = IOVector (Map k v)

-- insert a pair (key, value) into the IOMapMap
-- ensures: it replaces the existing mapping, if existing
insert :: (Ord k) => IORef (IOMapMap k v) -> Int -> k -> v -> IO ()
insert mmref idx key val = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    then MV.unsafeModify mm (Map.insert key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Map.empty) [len..(newLen-1)]
               ; MV.modify grown (Map.insert key val) idx
               ; writeIORef mmref grown
               }

-- insert a pair (key, value) into the IOMapMap
-- ensures: it uses the supplied combining function if the mapping is already present
insertWith :: (Ord k) => IORef (IOMapMap k v) -> Int -> (v -> v -> v) -> k -> v -> IO ()
insertWith mmref idx f key val = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    then MV.unsafeModify mm (Map.insertWith f key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Map.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Map.insert key val) idx
               ; writeIORef mmref grown
               }

lookup :: IORef (IOMapMap k v) -> Int -> IO [(k,v)]
lookup mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.toList <$> MV.read mm idx
    else return []

lookupValue :: (Ord k) => IORef (IOMapMap k v) -> Int -> k -> IO (Maybe v)
lookupValue mmref idx mapIdx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.lookup mapIdx <$> MV.read mm idx
    else return Nothing
 
delete :: Ord k => IORef (IOMapMap k v) -> (Int, k) -> IO ()
delete mmref (idx, mapIdx) = do
  mm <- readIORef mmref
  when (idx < MV.length mm) $ MV.unsafeModify mm (Map.delete mapIdx) idx

-- check the presence of the key in the Map at StateId position
member :: (Ord k) => IORef (IOMapMap k v) -> Int -> k -> IO Bool
member mmref idx key = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.member key <$> MV.unsafeRead mm idx
    else return False

-- an empty Map Map, an array of maps
empty :: IO (IORef (IOMapMap k v))
empty = do
  mm <- MV.replicate 4 Map.empty
  newIORef mm

foldMaps :: (Ord k) => IORef (IOMapMap k v) -> IO (Map (Int,k) v)
foldMaps mmref = do 
  mm <- readIORef mmref 
  MV.ifoldl' (\acc idx m -> Map.union acc . Map.mapKeys (\k -> (idx, k)) $ m) Map.empty mm

-- for debugging purposes
showIOMapMap :: (Show  k, Show v) => IOMapMap k v -> IO String
showIOMapMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Map at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""

