{- |
   Module      : Pomc.SetMap
   Copyright   : 2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari,Francesco Pontiggia
-}

module Pomc.SetMap ( SetMap
                   , insert
                   , lookup
                   , member
                   , modifyAll
                   , empty
                   ) where

import Prelude hiding (lookup)
import Pomc.SatUtil
import Control.Monad(mapM, mapM_)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Vector.Mutable as MV

-- Map to sets
type SetMap s v = MV.MVector s (Set v)

-- insert a state into the SetMap
insert :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s ()
insert smref stateid val = do
  sm <- readSTRef smref
  let len = MV.length sm
      sid = getId stateid
  if sid < len
    then MV.unsafeModify sm (Set.insert val) sid
    else let newLen = computeLen len sid
             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Set.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Set.insert val) sid
               ; writeSTRef smref grown
               }

lookup :: STRef s (SetMap s v) -> StateId state -> ST.ST s (Set v)
lookup smref stateid = do
  sm <- readSTRef smref
  let sid = getId stateid
  if sid < MV.length sm
    then MV.unsafeRead sm sid
    else return Set.empty

-- check whether a couple (StateId, Stack) iha already been visited checking the presence of the Stack in the Set at StateId position
member :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s Bool
member smref stateid val = do
  vset <- lookup smref stateid
  return $ val `Set.member` vset

modifyAll :: (Ord v) => STRef s (SetMap s v) -> (v -> v) -> ST.ST s ()
modifyAll smref f = do 
  sm <- readSTRef smref
  mapM_ (MV.unsafeModify sm $ Set.map f) [0..((MV.length sm) -1)] 

-- an empty Set Map, an array of sets
empty :: ST.ST s (STRef s (SetMap s v))
empty = do
  sm <- MV.replicate 4 Set.empty
  newSTRef sm 