{- |
   Module      : Pomc.GStack
   Copyright   : 2021-2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.GStack ( GStack
                   , new
                   , push
                   , peek
                   , safePeek
                   , multPeek
                   , pop
                   , pop_
                   , size
                   , multPop
                   , popWhile_
                   ) where

import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe (listToMaybe)

-- an implementation for a stack 
-- needed in the Gabow algorithm
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

safePeek :: GStack s v -> ST s (Maybe v)
safePeek (gsref, _)  = listToMaybe <$> readSTRef gsref

-- requires: the stack must be non empty
peek :: GStack s v -> ST s v
peek (gsref, _)  = head <$> readSTRef gsref

-- requires: the stack must contain at leat n elements
multPeek :: GStack s v -> Int -> ST s [v]
multPeek (gsref, _) n = take n <$> readSTRef gsref

-- requires: the stack must be non empty
pop :: GStack s v -> ST s v
pop (gsref, lenref)  = do
  gs <- readSTRef gsref
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref (+(-1))
  return $ head gs

-- requires: the stack must be non empty
pop_ :: GStack s v -> ST s ()
pop_ (gsref, lenref)  = do
  gs <- readSTRef gsref
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref (+(-1))

size :: GStack s v -> ST s Int
size (_, lenref) = readSTRef lenref

-- requires: the condition must hold before reaching the bottom of the stack
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

-- ensures: the returned list respects the previous order on the stack (first element of the returned list = top stack element)
multPop :: GStack s v -> Int  -> ST s [v]
multPop (gsref, lenref) n = do 
  (prefix, remainder) <- splitAt n <$> readSTRef gsref 
  writeSTRef gsref remainder 
  modifySTRef' lenref (+(-n))
  return prefix