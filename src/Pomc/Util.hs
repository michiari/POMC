{- |
   Module      : Pomc.Util
   Copyright   : 2020-2023 Davide Bergamaschi and Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Util ( any'
                 , iff
                 , implies
                 , xor
                 , safeHead
                 , safeTail
                 , timeFunApp
                 , timeAction
                 , timeToString
                 , parMap
                 , parMapChunk
                 ) where

import Data.Foldable (foldl')
import Control.Parallel.Strategies (using, parList, parListChunk, rdeepseq)
import Control.DeepSeq (NFData(..), force)
import Text.Printf (printf)
import GHC.Clock
import Control.Monad.IO.Class (MonadIO, liftIO)

any' :: Foldable t => (a -> Bool) -> t a -> Bool
any' p = foldl' (\z x -> z || p x) False

xor :: Bool -> Bool -> Bool
xor = (/=)

implies :: Bool -> Bool -> Bool
implies a b = (not a) || b

iff :: Bool -> Bool -> Bool
iff = (==)

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs

timeFunApp :: (MonadIO m, NFData c) => (b -> c) -> (a -> b) -> a -> m (b, Double)
timeFunApp toForce f x = timeAction toForce $ return $ f x

timeAction :: (MonadIO m, NFData b) => (a -> b) -> m a -> m (a, Double)
timeAction toForce action = do
  t1 <- liftIO getMonotonicTimeNSec
  a <- action
  _ <- return $! force (toForce a)
  t2 <- liftIO getMonotonicTimeNSec
  return (a, fromIntegral (t2 - t1) * 1e-9)

-- Adapted from Criterion.Measurement.secs by Bryan O'Sullivan
timeToString :: Double -> String
timeToString k
  | k < 0      = '-' : timeToString (-k)
  | k >= 1     = k        `with` "s"
  | k >= 1e-3  = (k*1e3)  `with` "ms"
  | k >= 1e-6  = (k*1e6)  `with` "μs"
  | k >= 1e-9  = (k*1e9)  `with` "ns"
  | k >= 1e-12 = (k*1e12) `with` "ps"
  | k >= 1e-15 = (k*1e15) `with` "fs"
  | k >= 1e-18 = (k*1e18) `with` "as"
  | otherwise  = printf "%g s" k
  where with :: Double -> String -> String
        with t u
          | t >= 1e9  = printf "%.4g %s" t u
          | t >= 1e3  = printf "%.0f %s" t u
          | t >= 1e2  = printf "%.1f %s" t u
          | t >= 1e1  = printf "%.2f %s" t u
          | otherwise = printf "%.3f %s" t u

-- a map where the function is applied (with reduction to normal form) to all the elements of the list in parallel
parMap :: (NFData b) => (a -> b) -> [a] -> [b]
parMap f xs = map f xs `using` parList rdeepseq

parMapChunk :: (NFData b) => Int -> (a -> b) -> [a] -> [b]
parMapChunk n f xs = map f xs `using` parListChunk n rdeepseq
