{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module POMC.Prec ( Prec(..)
                 , composePrecFunc
                 , predPrecRule
                 , structPrecRule
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

composePrecFunc :: [PrecFunc a] -> PrecFunc a
composePrecFunc precRules = apply precRules
  where apply       [] s1 s2 = Nothing
        apply (pr:prs) s1 s2 = case pr s1 s2 of
                                 Just prec -> Just prec
                                 Nothing   -> apply prs s1 s2

predPrecRule :: (Set (Prop a) -> Set (Prop a) -> Bool) -> Prec -> PrecFunc a
predPrecRule pred prec = \s1 s2 -> if pred s1 s2 then Just prec else Nothing

structPrecRule :: Ord a => Prop a -> Prop a -> Prec -> PrecFunc a
structPrecRule p1 p2 prec =
  predPrecRule (\s1 s2 -> p1 `S.member` s1 && p2 `S.member` s2) prec
