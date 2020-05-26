{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module POMC.Prec ( Prec(..)
                 , compose
                 , fromPredicate
                 , fromRelation
                 , fromRelations
                 ) where

import POMC.Prop (Prop)

import Control.DeepSeq
import GHC.Generics (Generic)

import Data.Set (Set)
import qualified Data.Set as S

data Prec = Yield | Equal | Take deriving (Eq, Ord, Generic, NFData)

instance Show Prec where
  show Yield = "<"
  show Equal = "="
  show Take  = ">"

type PrecFunc a = Set (Prop a) -> Set (Prop a) -> Maybe Prec
type PrecRel a = (Set (Prop a), Set (Prop a), Prec)

compose :: [PrecFunc a] -> PrecFunc a
compose precRules = apply precRules
  where apply       [] s1 s2 = Nothing
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
