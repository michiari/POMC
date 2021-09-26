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
                   , popUntil
                   ) where

import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')

-- an implementation for the stack needed in the Gabow algorithm
type GStack s v = (STRef s [v], STRef s Int)

new :: ST.ST s (GStack s v)
new = do 
  stack <- newSTRef []
  len <- newSTRef (0::Int)
  return (stack,len)

push :: GStack s v -> v -> ST.ST s ()
push (gsref, lenref) val = do 
  modifySTRef' gsref $ \l -> val:l;
  modifySTRef' lenref (+1)

peek :: GStack s v -> ST.ST s v
peek (gsref, _)  = do
  gs <- readSTRef gsref 
  return $ head gs

pop :: GStack s v -> ST.ST s v
pop (gsref, lenref)  = do
  gs <- readSTRef gsref 
  writeSTRef gsref $ tail gs;
  modifySTRef' lenref (+(-1))
  return $ head gs

size :: GStack s v -> ST.ST s Int
size (_, lenref) = readSTRef lenref

popUntil :: GStack s v -> ST.ST s Bool -> ST.ST s [v]
popUntil gs cond = 
  let recurse acc = do 
        condEval <- cond  
        if condEval 
          then return acc  
          else do 
            x <- pop gs 
            recurse (x:acc)
  in recurse []

