{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Prec
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Prec ( -- * Main precedence type
                   Prec(..)
                 , PrecSet(..)
                 , empty
                 , singleton
                 , size
                 , member
                 , notMember
                 , fromList
                 , toList
                   -- * Precedence function utilities
                 , PrecFunc
                 , PrecRel
                 , StructPrecRel
                 , compose
                 , fromPredicate
                 , fromRelation
                 , fromRelations
                 , fromStructPR
                 , extractSLs
                 , addEnd
                 ) where

import Pomc.Prop (Prop(..))

import GHC.Generics (Generic)
import Data.Hashable
import Data.List (find)
import Data.Containers.ListUtils (nubOrd)
import Data.Maybe (fromJust)
import Data.Bits (Bits(..))

import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.Map as M

data Prec = Yield | Equal | Take deriving (Eq, Ord, Generic)

instance Hashable Prec

instance Show Prec where
  show Yield = "<"
  show Equal = "="
  show Take  = ">"

newtype PrecSet = PrecSet Word deriving (Eq, Ord, Generic)

instance Hashable PrecSet

instance Show PrecSet where
  show = show . toList

empty :: PrecSet
empty = PrecSet 0

singleton :: Prec -> PrecSet
singleton = PrecSet . mask

size :: PrecSet -> Int
size (PrecSet pset) = popCount pset

member :: Prec -> PrecSet -> Bool
member p (PrecSet pset) = pset .&. (mask p) /= 0

notMember :: Prec -> PrecSet -> Bool
notMember p (PrecSet pset) = pset .&. (mask p) == 0

fromList :: [Prec] -> PrecSet
fromList plist = PrecSet $ foldl (\pset prec -> pset .|. mask prec) 0 plist

toList :: PrecSet -> [Prec]
toList pset = filter (\prec -> prec `member` pset) [Yield, Equal, Take]

mask :: Prec -> Word
mask Yield = 1
mask Equal = 2
mask Take  = 4


type PrecFunc a = Set (Prop a) -> Set (Prop a) -> Maybe Prec
type PrecRel a = (Set (Prop a), Set (Prop a), Prec)
type StructPrecRel a = (Prop a, Prop a, Prec)

compose :: [PrecFunc a] -> PrecFunc a
compose precRules = apply precRules
  where apply       [] _ _ = Nothing
        apply (pr:prs) s1 s2 = case pr s1 s2 of
                                 Just prec -> Just prec
                                 Nothing   -> apply prs s1 s2

fromPredicate :: (Set (Prop a) -> Set (Prop a) -> Bool) -> Prec -> PrecFunc a
fromPredicate predicate prec = \s1 s2 -> if predicate s1 s2 then Just prec else Nothing

fromRelation :: Ord a => PrecRel a -> PrecFunc a
fromRelation (sb1, sb2, prec) = \s1 s2 -> if (sb1 `S.isSubsetOf` s1) &&
                                             (sb2 `S.isSubsetOf` s2)
                                            then Just prec
                                            else Nothing

fromRelations :: Ord a => [PrecRel a] -> PrecFunc a
fromRelations prs = compose (map fromRelation prs)

-- Build precedence function from list of precedence relations
-- between structural labels. The resulting function raises an
-- exception if an input set  does not contain any structural labels,
-- and does not check if there are more than one.
fromStructPR :: Ord a => [StructPrecRel a] -> PrecFunc a
fromStructPR sprs = \s1 s2 -> M.lookup (structLabel s1, structLabel s2) relMap
  where structLabel s = fromJust $ find (\p -> S.member p s) (extractSLs sprs)
        relMap = M.fromList $ map (\(sl1, sl2, pr) -> ((sl1, sl2), pr)) sprs

extractSLs :: Ord a => [StructPrecRel a] -> [Prop a]
extractSLs sprs = nubOrd $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) sprs

addEnd :: Ord a => [StructPrecRel a] -> [StructPrecRel a]
addEnd sprs = sprs ++ map (\p -> (p, End, Take)) (extractSLs sprs)
