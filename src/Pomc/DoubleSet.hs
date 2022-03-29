{- |
   Module      : Pomc.DoubleSet
   Copyright   : 2022 Francesco Pontiggia
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

import Data.Set(Set)
import qualified Data.Set as Set

-- an implementation for a set where some elements are marked
-- needed for the set of initial nodes of the SCC algorithm
type DoubleSet s v = STRef s (Set v, Set v)

new :: ST s (DoubleSet s v)
new = newSTRef (Set.empty, Set.empty)

insert :: (Ord v) => DoubleSet s v -> (v, Bool) -> ST s ()
insert dsref (v,b) = modifySTRef' dsref $ \(ds1, ds2) -> 
  if b 
    then (Set.insert v ds1, ds2)
    else (ds1, Set.insert v ds2)

unmark :: (Ord v) => DoubleSet s v -> v -> ST s ()
unmark dsref v = modifySTRef' dsref $ \(ds1, ds2) -> 
  if Set.member v ds1 
    then (Set.delete v ds1, Set.insert v ds2)
    else (ds1,ds2)

markAll :: (Ord v) => DoubleSet s v -> ST s ()
markAll dsref = modifySTRef' dsref $ \(ds1, ds2) -> (Set.union ds2 ds1, Set.empty)

reset :: (Ord v) => DoubleSet s v  -> ST s ()
reset dsref = writeSTRef dsref (Set.empty, Set.empty)

isMarked :: (Ord v) => DoubleSet s v -> v -> ST s Bool
isMarked dsref v = do 
  (ds1, _) <- readSTRef dsref 
  return $ Set.member v ds1

isNotMarked :: (Ord v) => DoubleSet s v -> v -> ST s Bool
isNotMarked dsref v = do 
  (ds1, _) <- readSTRef dsref 
  return $ not $ Set.member v ds1

allMarked :: (Ord v) => DoubleSet s v -> ST s (Set v)
allMarked dsref = do 
  (ds1, _) <- readSTRef dsref 
  return ds1