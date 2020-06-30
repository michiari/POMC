{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Prec
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Prec ( -- * Main precedence type
                   Prec(..)
                   -- * Precedence function utilities
                 , PrecFunc
                 , PrecRel
                 , StructPrecRel
                 , compose
                 , fromPredicate
                 , fromRelation
                 , fromRelations
                 , fromStructPR
                 ) where

import Pomc.Prop (Prop)

import Control.DeepSeq
import GHC.Generics (Generic)
import Data.Hashable
import Data.List (nub, find)
import Data.Maybe (fromJust)

import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.Map as M

data Prec = Yield | Equal | Take deriving (Eq, Ord, Generic, NFData)

instance Hashable Prec

instance Show Prec where
  show Yield = "<"
  show Equal = "="
  show Take  = ">"

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
fromPredicate pred prec = \s1 s2 -> if pred s1 s2 then Just prec else Nothing

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
  where sl = nub $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) sprs
        structLabel s = fromJust $ find (\p -> S.member p s) sl
        relMap = M.fromList $ map (\(sl1, sl2, pr) -> ((sl1, sl2), pr)) sprs
