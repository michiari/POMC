module POMC.Prec ( makePrecFunc
                 , predPrecRule
                 ) where

import POMC.RPotl (Prop)
import POMC.Opa (Prec (..))

import Data.Set (Set)
import qualified Data.Set as S

type PrecRule a = Set (Prop a) -> Set (Prop a) -> Maybe Prec

makePrecFunc :: [PrecRule a] -> (Set (Prop a) -> Set (Prop a) -> Maybe Prec)
makePrecFunc precRules = apply precRules
  where apply       [] s1 s2 = Nothing
        apply (pr:prs) s1 s2 = case pr s1 s2 of
                                 Just prec -> Just prec
                                 Nothing   -> apply prs s1 s2

predPrecRule :: (Set (Prop a) -> Set (Prop a) -> Bool) -> Prec -> PrecRule a
predPrecRule pred prec = \s1 s2 -> if pred s1 s2 then Just prec else Nothing

structPrecRule :: Ord a => Prop a -> Prop a -> Prec -> PrecRule a
structPrecRule p1 p2 prec =
  predPrecRule (\s1 s2 -> p1 `S.member` s1 && p2 `S.member` s2) prec
