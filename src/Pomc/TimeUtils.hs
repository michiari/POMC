{- |
   Module      : Pomc.TimeUtils
   Copyright   : 2020-2023 Davide Bergamaschi and Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.TimeUtils ( timeFunApp
                      , timeAction
                      , timeToString
                      ) where

import Text.Printf (printf)
import GHC.Clock
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.DeepSeq (NFData, force)

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
