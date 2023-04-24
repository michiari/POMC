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
                 , timeAction
                 , timeToString
                 , parMap
                 , parMapChunk
                 ) where

import Data.Foldable (foldl')
import Criterion.Measurement (initializeTime, getTime, secs)
import Control.Parallel.Strategies (using, parList, parListChunk, rdeepseq)
import Control.DeepSeq (NFData(..))


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

timeAction :: IO a -> IO (a, Double)
timeAction action = do initializeTime
                       t1 <- getTime
                       a  <- action
                       t2 <- getTime
                       return (a, (t2 - t1))

timeToString :: Double -> String
timeToString = secs

-- a map where the function is applied (with reduction to normal form) to all the elements of the list in parallel
parMap :: (NFData b) => (a -> b) -> [a] -> [b]
parMap f xs = map f xs `using` parList rdeepseq

parMapChunk :: (NFData b) => Int -> (a -> b) -> [a] -> [b]
parMapChunk n f xs = map f xs `using` parListChunk n rdeepseq
