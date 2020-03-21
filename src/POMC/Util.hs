module POMC.Util ( unsafeLookup
                 , lookupOrDefault
                 , xor
                 , implies
                 , iff
                 ) where

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup k al = case lookup k al of
  Just v  ->  v
  Nothing ->  error "Failed lookup!"

lookupOrDefault :: Eq a => a -> [(a,b)] -> b -> b
lookupOrDefault k al d = case lookup k al of
  Just v  ->  v
  Nothing ->  d

xor :: Bool -> Bool -> Bool
xor = (/=)

implies :: Bool -> Bool -> Bool
implies a b = (not a) || b

iff :: Bool -> Bool -> Bool
iff = (==)
