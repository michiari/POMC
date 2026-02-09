{- |
   Module      : Pomc.IOIOMapMap
   Copyright   : 2024-2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.IOMapMap ( IOMapMap
                   , insert
                   , insertWith
                   , insertMap
                   , lookup
                   , lookupMap
                   , lookupKeys
                   , lookupValue
                   , member
                   , delete
                   , empty
                   , emptySized
                   , showIOMapMap
                   , values
                   , valuesWith
                   ) where

import Prelude hiding (lookup)
import qualified Data.Vector.Mutable as MV
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.IORef (readIORef, IORef, newIORef, writeIORef)
import Data.Vector.Mutable (IOVector)
import Control.Monad(when)

-- Map to Maps
type IOMapMap v = IOVector (IntMap v)

-- insert a pair (key, value) into the IOMapMap
-- ensures: it replaces the existing mapping, if existing
insert :: IORef (IOMapMap v) -> Int -> Int -> v -> IO ()
insert mmref idx key val = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    then MV.unsafeModify mm (IntMap.insert key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i IntMap.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (IntMap.insert key val) idx
               ; writeIORef mmref grown
               }

-- insert a pair (key, value) into the IOMapMap
-- ensures: it replaces the existing mapping, if existing
insertMap :: IORef (IOMapMap v) -> Int -> IntMap v -> IO ()
insertMap mmref idx m = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    -- union is left-biased, so we prefer new values to old ones in case of overlapping keys
    then MV.unsafeModify mm (IntMap.union m) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i IntMap.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (IntMap.union m) idx
               ; writeIORef mmref grown
               }

-- insert a pair (key, value) into the IOMapMap
-- ensures: it uses the supplied combining function if the mapping is already present
insertWith :: IORef (IOMapMap v) -> Int -> (v -> v -> v) -> Int -> v -> IO ()
insertWith mmref idx f key val = do
  mm <- readIORef mmref
  let len = MV.length mm
  if idx < len
    then MV.unsafeModify mm (IntMap.insertWith f key val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i IntMap.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (IntMap.insert key val) idx
               ; writeIORef mmref grown
               }

lookup :: IORef (IOMapMap v) -> Int -> IO [(Int,v)]
lookup mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then IntMap.toList <$> MV.unsafeRead mm idx
    else return []

lookupMap :: IORef (IOMapMap v) -> Int -> IO (IntMap v)
lookupMap mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then MV.unsafeRead mm idx
    else return IntMap.empty

lookupKeys :: IORef (IOMapMap v) -> Int -> IO IntSet
lookupKeys mmref idx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then IntMap.keysSet <$> MV.unsafeRead mm idx
    else return IntSet.empty

lookupValue :: IORef (IOMapMap v) -> Int -> Int -> IO (Maybe v)
lookupValue mmref idx mapIdx = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then IntMap.lookup mapIdx <$> MV.unsafeRead mm idx
    else return Nothing

delete :: IORef (IOMapMap v) -> Int -> Int -> IO ()
delete mmref idx mapIdx = do
  mm <- readIORef mmref
  when (idx < MV.length mm) $ MV.unsafeModify mm (IntMap.delete mapIdx) idx

-- check the presence of the key in the Map at StateId position
member :: IORef (IOMapMap v) -> Int -> Int -> IO Bool
member mmref idx key = do
  mm <- readIORef mmref
  if idx < MV.length mm
    then IntMap.member key <$> MV.unsafeRead mm idx
    else return False

-- an empty Map Map, an array of maps
empty :: IO (IORef (IOMapMap v))
empty = do
  mm <- MV.replicate 4 IntMap.empty
  newIORef mm

-- an empty Map Map, an array of maps
emptySized :: Int -> IO (IORef (IOMapMap v))
emptySized l = do
  mm <- MV.replicate l IntMap.empty
  newIORef mm

values :: IORef (IOMapMap v) -> IO (Vector [v])
values mmref = do
  mm <- readIORef mmref
  V.map IntMap.elems <$> V.freeze mm

valuesWith :: IORef (IOMapMap v) -> (v -> w) -> IO (Vector [w])
valuesWith mmref f = do
  mm <- readIORef mmref
  V.map (map f . IntMap.elems) <$> V.freeze mm

-- for debugging purposes
showIOMapMap :: (Show v) => IOMapMap v -> IO String
showIOMapMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Map at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""