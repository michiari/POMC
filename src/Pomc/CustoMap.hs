{- |
   Module      : Pomc.CustoMap
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.CustoMap ( CustoMap
                     , empty
                     , emptySized
                     , insert
                     , lookup
                     , modify
                     , multModify
                     , modifyAll
                     , take
                     , showMap
                     , showSTRefMap
                     ) where

import Prelude hiding (lookup, take)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import Data.List(nub)

import qualified Data.Vector.Mutable as MV

-- a custom mutable Map
type CustoMap s v = MV.MVector s v

empty :: ST.ST s (STRef s (CustoMap s v))
empty = newSTRef =<< MV.new 4

emptySized :: Int -> ST.ST s (STRef s (CustoMap s v))
emptySized size = newSTRef =<< MV.new size

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

modify :: STRef s (CustoMap s v) -> (v -> v) -> Int -> ST.ST s ()
modify cmref f k = do
  cm <- readSTRef cmref
  MV.unsafeModify cm f k

multModify :: STRef s (CustoMap s v) -> (v -> v) -> [Int] -> ST.ST s ()
multModify cmref f keys = do
  cm <- readSTRef cmref
  mapM_ (MV.unsafeModify cm f) $ nub keys

modifyAll :: STRef s (CustoMap s v) -> (v -> v) -> Int -> ST.ST s ()
modifyAll cmref f len = do
  cm <- readSTRef cmref
  mapM_ (MV.unsafeModify cm f) [0..(len -1)]

-- removing uninitialized elements
take :: Int -> CustoMap s v -> CustoMap s v
take = MV.unsafeTake

-- for debugging purposes
showMap :: (Show  v) => CustoMap s v -> ST.ST s String
showMap = MV.ifoldl'
    (\acc idx el -> acc ++ "Element at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""

showSTRefMap :: (Show  v) => STRef s (CustoMap s v) -> ST.ST s String
showSTRefMap cmref = do 
  cm <- readSTRef cmref
  MV.ifoldl'
    (\acc idx el -> acc ++ "Element at position " ++ show idx ++ " : " ++ show el ++ "\n\n")
    ""
    cm
