{- |
   Module      : Pomc.GStack
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.GStack ( GStack
                   , push
                   , peek
                   , pop
                   , size
                   , new
                   , modifyAll
                   , allUntil
                   ) where

import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')

type GStack s v = (STRef s [v], STRef s Int)

push :: GStack s v -> v -> ST.ST s ()
push (gsref, lenref) val = do 
  modifySTRef' gsref $ \l -> val:l;
  modifySTRef' lenref  (+1)

peek :: GStack s v -> ST.ST s v
peek (gsref,_)  = do
  gs <- readSTRef gsref 
  return $ head gs

pop :: GStack s v -> ST.ST s v
pop (gsref, lenref)  = do
  gs <- readSTRef gsref 
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref  (+(-1))
  return $ head gs

-- slow
size :: GStack s v -> ST.ST s Int
size (_, lenref) = readSTRef lenref

  
-- an empty Set Map, an array of sets
new :: ST.ST s (GStack s v)
new = do 
  stack <- newSTRef []
  len <- newSTRef (0::Int)
  return (stack,len)

modifyAll :: (GStack s v) -> (v -> v) -> ST.ST s ()
modifyAll (gsref,_) f = modifySTRef' gsref $ map f

-- get all the elements on the stack until a certain condition holds (without popping them)
allUntil :: GStack s v -> (v -> ST.ST s Bool)  -> ST.ST s [v]
allUntil (gsref,_) cond = 
  let recurse acc (x:xs) = do 
        condEval <- cond x 
        if condEval 
          then return acc 
          else recurse (x:acc) xs 
  in do 
  gs <- readSTRef gsref 
  recurse [] gs