module POMC.Util ( unsafeLookup
                 , lookupOrDefault
                 , any'
                 , iff
                 , implies
                 , xor
                 , safeHead
                 , safeTail
                 , timeAction
                 ) where

import Data.Foldable (foldl')

import Criterion.Measurement (initializeTime, getTime, getCPUTime, secs)

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup k al = case lookup k al of
  Just v  ->  v
  Nothing ->  error "Failed lookup!"

lookupOrDefault :: Eq a => a -> [(a,b)] -> b -> b
lookupOrDefault k al d = case lookup k al of
  Just v  ->  v
  Nothing ->  d

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

timeAction :: IO a -> IO (a, String, String)
timeAction action = do initializeTime
                       t1 <- getTime
                       ct1 <- getCPUTime
                       a  <- action
                       t2 <- getTime
                       ct2 <- getCPUTime
                       return (a, secs(t2 - t1), secs(ct2 - ct1))
