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
                     , take
                     , showMap
                     ) where

import Prelude hiding (lookup, take)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import qualified Data.Vector.Mutable as MV

-- a custom mutable Map
type CustoMap s v = MV.MVector s v

empty :: ST.ST s (STRef s (CustoMap s v))
empty = do
  cm <- MV.new 4
  newSTRef cm

insert :: STRef s (CustoMap s v) -> Int -> v -> ST.ST s ()
insert cmref k val = do
  cm <- readSTRef cmref
  let len = MV.length cm
  if k < len
    then MV.unsafeWrite cm k val
    else let newLen = computeLen len k
             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow cm (newLen-len)
               ; MV.unsafeWrite grown k val
               ; writeSTRef cmref grown
               }

lookup :: STRef s (CustoMap s v) -> Int -> ST.ST s v
lookup cmref k  = do
  cm <- readSTRef cmref
  MV.unsafeRead cm k

modify :: STRef s (CustoMap s v) -> Int -> (v -> v) -> ST.ST s ()
modify cmref k f = do
  cm <- readSTRef cmref
  MV.unsafeModify cm f k

-- removing uninitialized elements
take :: Int -> CustoMap s v -> CustoMap s v
take = MV.unsafeTake

-- for debugging purposes
showMap :: (Show  v) => CustoMap s v -> ST.ST s String
showMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Element at position " ++ show idx ++ " : " ++ show el ++ "\n")
    ""
