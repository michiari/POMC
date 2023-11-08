{- |
   Module      : Pomc.DoubleSet
   Copyright   : 2022-2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.DoubleSet (DoubleSet
                   , new
                   , insert
                   , unmark
                   , markAll
                   , reset
                   , isMarked
                   , isNotMarked
                   , allMarked
                   ) where

import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

-- an implementation for a set where some elements are marked
-- needed for the set of initial nodes of the SCC algorithm
type DoubleSet s = STRef s (IntSet, IntSet)

new :: ST s (DoubleSet s)
new = newSTRef (IntSet.empty, IntSet.empty)

insert :: DoubleSet s -> (Int, Bool) -> ST s ()
insert dsref (v,b) = modifySTRef' dsref $ \(ds1, ds2) -> 
  if b 
    then (IntSet.insert v ds1, ds2)
    else (ds1, IntSet.insert v ds2)

unmark :: DoubleSet s -> Int -> ST s ()
unmark dsref v = modifySTRef' dsref $ \(ds1, ds2) -> 
  if IntSet.member v ds1 
    then (IntSet.delete v ds1, IntSet.insert v ds2)
    else (ds1,ds2)

markAll :: DoubleSet s -> ST s ()
markAll dsref = modifySTRef' dsref $ \(ds1, ds2) -> (IntSet.union ds2 ds1, IntSet.empty)

reset :: DoubleSet s -> ST s ()
reset dsref = writeSTRef dsref (IntSet.empty, IntSet.empty)

isMarked :: DoubleSet s -> Int -> ST s Bool
isMarked dsref v = do 
  (ds1, _) <- readSTRef dsref 
  return $ IntSet.member v ds1

isNotMarked :: DoubleSet s -> Int -> ST s Bool
isNotMarked dsref v = do 
  (ds1, _) <- readSTRef dsref 
  return $ not $ IntSet.member v ds1

allMarked :: DoubleSet s -> ST s IntSet
allMarked dsref = do 
  (ds1, _) <- readSTRef dsref 
  return ds1
