{- |
   Module      : Pomc.ZStack
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.ZStack ( ZStack
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

import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
import Data.Maybe (listToMaybe)

-- an implementation for a stack 
-- needed in Z3 encoding for probabilistic termination checking
type ZStack v = (IORef [v], IORef Int)

new :: IO (ZStack v)
new = do
  stack <- newIORef []
  len <- newIORef (0::Int)
  return (stack,len)

push :: ZStack v -> v -> IO ()
push (gsref, lenref) val = do
  modifyIORef' gsref $ \l -> val:l;
  modifyIORef' lenref (+1)

safePeek :: ZStack v -> IO (Maybe v)
safePeek (gsref, _)  = listToMaybe <$> readIORef gsref

-- requires: the stack must be non empty
peek :: ZStack v -> IO v
peek (gsref, _)  = head <$> readIORef gsref

-- requires: the stack must contain at leat n elements
multPeek :: ZStack v -> Int -> IO [v]
multPeek (gsref, _) n = take n <$> readIORef gsref

-- requires: the stack must be non empty
pop :: ZStack v -> IO v
pop (gsref, lenref)  = do
  gs <- readIORef gsref
  writeIORef gsref $ tail gs;
  modifyIORef' lenref (+(-1))
  return $ head gs

-- requires: the stack must be non empty
pop_ :: ZStack v -> IO ()
pop_ (gsref, lenref)  = do
  gs <- readIORef gsref
  writeIORef gsref $ tail gs;
  modifyIORef' lenref (+(-1))

size :: ZStack v -> IO Int
size (_, lenref) = readIORef lenref

-- requires: the condition must hold before reaching the bottom of the stack
popWhile_ :: ZStack v -> (v -> Bool) -> IO ()
popWhile_ (gsref, lenref) cond = 
  let 
    recurse True  gs l  = recurse (cond . head . tail $ gs) (tail gs) (l+(-1)) 
    recurse False gs l  = do 
      writeIORef gsref gs 
      writeIORef lenref l 
      return ()
  in do 
    gs <- readIORef gsref
    l <- readIORef lenref
    recurse (cond $ head gs) gs l 

-- ensures: the returned list respects the previous order on the stack (first element of the returned list = top stack element)
multPop :: ZStack v -> Int  -> IO [v]
multPop (gsref, lenref) n = do 
  (prefix, remainder) <- splitAt n <$> readIORef gsref 
  writeIORef gsref remainder 
  modifyIORef' lenref (+(-n))
  return prefix