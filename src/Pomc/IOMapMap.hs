{- |
   Module      : Pomc.IOIOMapMap
   Copyright   : 2024 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.IOMapMap ( IOMapMap
                   , insert
                   , insertWith
                   , insertMap
                   , lookup
                   , lookupKeys
                   , lookupValue
                   , member
                   , delete
                   , empty
                   , showIOMapMap
                   , foldMaps
                   ) where

import Prelude hiding (lookup)

import qualified Data.Vector.Mutable as MV

import qualified Data.IntMap as Map
import Data.IntMap(IntMap)

import Data.Map(Map)
import qualified Data.Map as GM
import Data.IORef (readIORef, IORef, newIORef, writeIORef)
import Data.Vector.Mutable (IOVector)

import Control.Monad(when)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- Map to Maps
type IOMapMap v = IOVector (IntMap v)

-- insert a pair (key, value) into the IOMapMap
-- ensures: it replaces the existing mapping, if existing
insert :: IORef (IOMapMap v) -> Int -> Int -> v -> IO ()
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
-- ensures: it replaces the existing mapping, if existing
insertMap :: IORef (IOMapMap v) -> Int -> IntMap v -> IO ()
insertMap mmref idx m = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    then MV.unsafeModify mm (Map.union m) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Map.empty) [len..(newLen-1)]
               ; MV.unsafeModify mm (Map.union m) idx
               ; writeIORef mmref grown
               }

-- insert a pair (key, value) into the IOMapMap
-- ensures: it uses the supplied combining function if the mapping is already present
insertWith :: IORef (IOMapMap v) -> Int -> (v -> v -> v) -> Int -> v -> IO ()
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

lookup :: IORef (IOMapMap v) -> Int -> IO [(Int,v)]
lookup mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.toList <$> MV.read mm idx
    else return []

lookupKeys :: IORef (IOMapMap v) -> Int -> IO IntSet
lookupKeys mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.keysSet <$> MV.read mm idx
    else return IntSet.empty

lookupValue :: IORef (IOMapMap v) -> Int -> Int -> IO (Maybe v)
lookupValue mmref idx mapIdx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.lookup mapIdx <$> MV.read mm idx
    else return Nothing

delete :: IORef (IOMapMap v) -> (Int, Int) -> IO ()
delete mmref (idx, mapIdx) = do
  mm <- readIORef mmref
  when (idx < MV.length mm) $ MV.unsafeModify mm (Map.delete mapIdx) idx

-- check the presence of the key in the Map at StateId position
member :: IORef (IOMapMap v) -> Int -> Int -> IO Bool
member mmref idx key = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then Map.member key <$> MV.unsafeRead mm idx
    else return False

-- an empty Map Map, an array of maps
empty :: IO (IORef (IOMapMap v))
empty = do
  mm <- MV.replicate 4 Map.empty
  newIORef mm

foldMaps :: IORef (IOMapMap v) -> IO (Map (Int,Int) v)
foldMaps mmref = do
  mm <- readIORef mmref
  MV.ifoldl' (\acc idx m -> GM.union acc . GM.fromList . map (\(k, i) -> ((idx, k), i)) . Map.toList $ m) GM.empty mm

-- for debugging purposes
showIOMapMap :: (Show v) => IOMapMap v -> IO String
showIOMapMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Map at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""

