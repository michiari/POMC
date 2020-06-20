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
                 , compose
                 , fromPredicate
                 , fromRelation
                 , fromRelations
                 ) where

import Pomc.Prop (Prop)
import Pomc.Util (isSubsetOf)

import Control.DeepSeq
import GHC.Generics (Generic)

import Data.Hashable

import Data.HashSet (HashSet)
import qualified Data.HashSet as S

data Prec = Yield | Equal | Take deriving (Eq, Ord, Generic, NFData)

instance Hashable Prec

instance Show Prec where
  show Yield = "<"
  show Equal = "="
  show Take  = ">"

type PrecFunc a = HashSet (Prop a) -> HashSet (Prop a) -> Maybe Prec
type PrecRel a = (HashSet (Prop a), HashSet (Prop a), Prec)

compose :: [PrecFunc a] -> PrecFunc a
compose precRules = apply precRules
  where apply       [] s1 s2 = Nothing
        apply (pr:prs) s1 s2 = case pr s1 s2 of
                                 Just prec -> Just prec
                                 Nothing   -> apply prs s1 s2

fromPredicate :: (HashSet (Prop a) -> HashSet (Prop a) -> Bool) -> Prec -> PrecFunc a
fromPredicate pred prec = \s1 s2 -> if pred s1 s2 then Just prec else Nothing

fromRelation :: (Ord a, Hashable a) => PrecRel a -> PrecFunc a
fromRelation (sb1, sb2, prec) = \s1 s2 -> if (sb1 `isSubsetOf` s1) &&
                                             (sb2 `isSubsetOf` s2)
                                            then Just prec
                                            else Nothing

fromRelations :: (Ord a, Hashable a) => [PrecRel a] -> PrecFunc a
fromRelations prs = compose (map fromRelation prs)
