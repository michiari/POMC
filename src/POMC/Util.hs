module POMC.Util ( unsafeLookup
                 , lookupOrDefault
                 ) where

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup k al = case lookup k al of
  Just v  ->  v
  Nothing ->  error "Failed lookup!"

lookupOrDefault :: Eq a => a -> [(a,b)] -> b -> b
lookupOrDefault k al d = case lookup k al of
  Just v  ->  v
  Nothing ->  d
