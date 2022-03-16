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
                   , pop_
                   , size
                   , new
                   , multPop
                   , popWhile
                   , popWhile_
                   ) where

import Control.Monad.ST (ST)
import Control.Monad(replicateM)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')

-- an implementation for the stack needed in the Gabow algorithm
type GStack s v = (STRef s [v], STRef s Int)

new :: ST s (GStack s v)
new = do
  stack <- newSTRef []
  len <- newSTRef (0::Int)
  return (stack,len)

push :: GStack s v -> v -> ST s ()
push (gsref, lenref) val = do
  modifySTRef' gsref $ \l -> val:l;
  modifySTRef' lenref (+1)

peek :: GStack s v -> ST s v
peek (gsref, _)  = do
  gs <- readSTRef gsref
  return $ head gs

pop :: GStack s v -> ST s v
pop (gsref, lenref)  = do
  gs <- readSTRef gsref
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref (+(-1))
  return $ head gs

pop_ :: GStack s v -> ST s ()
pop_ (gsref, lenref)  = do
  gs <- readSTRef gsref
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref (+(-1))
  return ()

size :: GStack s v -> ST s Int
size (_, lenref) = readSTRef lenref

multPop :: GStack s v -> Int  -> ST s [v]
multPop gs n  = replicateM n $ pop gs

popWhile :: GStack s v -> (v -> Bool) -> ST s [v]
popWhile (gsref, lenref) cond = 
  let 
    recurse True  gs l acc = recurse (cond . head . tail $ gs) (tail gs) (l+(-1)) ((head gs):acc)
    recurse False gs l acc = do 
      writeSTRef gsref gs 
      writeSTRef lenref l 
      return acc
  in do 
    gs <- readSTRef gsref
    l <- readSTRef lenref
    recurse (cond $ head gs) gs l [] 

popWhile_ :: GStack s v -> (v -> Bool) -> ST s ()
popWhile_ (gsref, lenref) cond = 
  let 
    recurse True  gs l  = recurse (cond . head . tail $ gs) (tail gs) (l+(-1)) 
    recurse False gs l  = do 
      writeSTRef gsref gs 
      writeSTRef lenref l 
      return ()
  in do 
    gs <- readSTRef gsref
    l <- readSTRef lenref
    recurse (cond $ head gs) gs l 

