{- |
   Module      : Pomc.IOIOSetMap
   Copyright   : 2024 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.IOSetMap ( IOSetMap
                   , insert
                   , lookup
                   , member
                   , empty
                   , showIOSetMap
                   ) where

import Prelude hiding (lookup)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV

-- Map to sets
type IOSetMap v = IOVector (Set v)

-- insert a state into the IOSetMap
insert :: (Ord v) => IORef (IOSetMap v) -> Int -> v -> IO ()
insert smref idx val = do
  sm <- readIORef smref
  let len = MV.length sm
  if idx < len
    then MV.unsafeModify sm (Set.insert val) idx
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Set.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Set.insert val) idx
               ; writeIORef smref grown
               }

lookup :: IORef (IOSetMap v) -> Int -> IO (Set v)
lookup smref idx = do
  sm <- readIORef smref
  if idx < MV.length sm
    then MV.unsafeRead sm idx
    else return Set.empty

-- check the presence of the Stack in the Set at StateId position
member :: (Ord v) => IORef (IOSetMap v) -> Int -> v -> IO Bool
member smref idx val = do
  vset <- lookup smref idx
  return $ val `Set.member` vset

-- an empty Set Map, an array of sets
empty :: IO (IORef (IOSetMap v))
empty = do
  sm <- MV.replicate 4 Set.empty
  newIORef sm

-- for debugging purposes
showIOSetMap :: (Show  v) => IOSetMap v -> IO String
showIOSetMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Set at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""
