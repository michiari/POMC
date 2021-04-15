{- |
   Module      : Pomc.SatUtil
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SatUtil ( debug
                     , freshPosId
                     , freshNegId
                     ) where


import Data.STRef (STRef, readSTRef, modifySTRef')

import Data.Maybe

import qualified Control.Monad.ST as ST

import Debug.Trace (trace)

debug :: String -> a -> a
debug _ x = x
--debug msg r = trace msg r 

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return $ curr

freshNegId :: STRef s Int -> ST.ST s Int
freshNegId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+(-1));
  return $ curr