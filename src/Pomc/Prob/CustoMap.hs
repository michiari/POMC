{- |
   Module      : Pomc.CustoMap
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.CustoMap ( CustoMap
                     , empty
                     , insert
                     , lookup
                     , modify
                     ) where

import Prelude hiding (lookup)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import qualified Data.Vector.Mutable as MV

-- a custom mutable Map
type CustoMap s v = MV.MVector s v

empty :: ST.ST s (STRef s (CustoMap s v))
empty = do
  mm <- MV.new 4
  newSTRef mm

insert :: STRef s (CustoMap s v) -> Int -> v -> ST.ST s ()
insert mmref k val = do
  mm <- readSTRef mmref
  let len = MV.length mm
  if k < len
    then MV.unsafeWrite mm k val
    else let newLen = computeLen len k
             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow mm (newLen-len)
               ; MV.unsafeWrite grown k val
               ; writeSTRef mmref grown
               }

lookup :: STRef s (CustoMap s v) -> Int -> ST.ST s v
lookup mmref k  = do
  mm <- readSTRef mmref
  MV.unsafeRead mm k

modify ::STRef s (CustoMap s v) -> Int -> (v -> v) -> ST.ST s ()
modify mmref k f = do
  mm <- readSTRef mmref
  MV.unsafeModify mm f k
