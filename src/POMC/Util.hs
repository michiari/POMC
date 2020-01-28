module POMC.Util ( trace
                 , unsafeLookup
                 , lookupOrDefault
                 ) where

import qualified Debug.Trace

trace :: (Show a) => a -> a
trace a = Debug.Trace.trace (show a) a

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup k al = case lookup k al of
  Just v  ->  v
  Nothing ->  error "Failed lookup!"

lookupOrDefault :: Eq a => a -> [(a,b)] -> b -> b
lookupOrDefault k al d = case lookup k al of
  Just v  ->  v
  Nothing ->  d
