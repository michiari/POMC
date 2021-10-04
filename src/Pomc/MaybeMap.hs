{- |
   Module      : Pomc.MaybeMap
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.MaybeMap ( MaybeMap
                   , empty
                   , insert
                   , lookup
                   , delete 
                   , modify
                   , multModify
                   , modifyAll
                   ) where

import Prelude hiding (lookup)
import Control.Monad(mapM_)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import qualified Data.Vector.Mutable as MV

-- Map to sets
type MaybeMap s v = MV.MVector s (Maybe v)

-- an empty Maybe Map, an array of Maybes
empty :: ST.ST s (STRef s (MaybeMap s v))
empty = do
  mm <- MV.replicate 4 Nothing
  newSTRef mm 

-- insert a value in the MaybeMap at the given position
insert :: STRef s (MaybeMap s v) -> Int -> v -> ST.ST s ()
insert mmref k val = do
  mm <- readSTRef mmref
  let len = MV.length mm
  if k < len
    then MV.unsafeWrite mm k (Just val) 
    else let newLen = computeLen len k
             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow mm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Nothing) [len..(newLen-1)]
               ; MV.unsafeWrite grown k (Just val) 
               ; writeSTRef mmref grown
               }

lookup :: STRef s (MaybeMap s v) -> Int  -> ST.ST s (Maybe v)
lookup mmref k  = do 
  mm <- readSTRef mmref
  MV.unsafeRead mm k

delete :: STRef s (MaybeMap s v) -> Int  -> ST.ST s ()
delete mmref k  = do 
  mm <- readSTRef mmref
  MV.unsafeWrite mm k Nothing 

modify ::STRef s (MaybeMap s v) -> Int -> (v -> v) -> ST.ST s ()
modify mmref k f = do 
  mm <- readSTRef mmref
  MV.unsafeModify mm  (fmap f) k

multModify :: STRef s (MaybeMap s v) -> [Int] -> (v -> v) -> ST.ST s ()
multModify mmref keys f = do 
  mm <- readSTRef mmref
  mapM_ (MV.unsafeModify mm $ fmap f) keys

modifyAll :: STRef s (MaybeMap s v) -> (v -> v) -> ST.ST s ()
modifyAll mmref f = do 
  mm <- readSTRef mmref
  mapM_ (MV.unsafeModify mm $ fmap f) [0..((MV.length mm) -1)] 

