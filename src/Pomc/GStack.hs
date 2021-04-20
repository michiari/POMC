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

type GStack s v = STRef s [v]

push :: GStack s v -> v -> ST.ST s ()
push gsref val = modifySTRef' gsref $ \l -> val:l

peek :: GStack s v -> ST.ST s v
peek gsref  = do
  gs <- readSTRef gsref 
  return $ head gs

pop :: GStack s v -> ST.ST s v
pop gsref  = do
  gs <- readSTRef gsref 
  writeSTRef gsref $ tail gs
  return $ head gs

-- slow
size :: GStack s v -> ST.ST s Int
size gsref = do 
  gs <- readSTRef gsref 
  return $ length gs
  
-- an empty Set Map, an array of sets
new :: ST.ST s (GStack s v)
new = newSTRef []

modifyAll :: (GStack s v) -> (v -> v) -> ST.ST s ()
modifyAll gsref f = modifySTRef' gsref $ map f

-- get all the elements on the stack until a certain condition holds (without popping them)
allUntil :: GStack s v -> (v -> ST.ST s Bool)  -> ST.ST s [v]
allUntil gsref cond = 
  let recurse acc (x:xs) = do 
        condEval <- cond x 
        if condEval 
          then return acc 
          else recurse (x:acc) xs 
  in do 
  gs <- readSTRef gsref 
  recurse [] gs