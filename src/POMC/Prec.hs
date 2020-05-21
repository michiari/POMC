module POMC.Prec ( makePrecFunc
                 ) where

import POMC.RPotl (Prop)
import POMC.Opa (Prec (..))

import Data.Set (Set)

type PrecRule = Set (Prop String) -> Set (Prop String) -> Maybe Prec

makePrecFunc :: [PrecRule] -> (Set (Prop String) -> Set (Prop String) -> Prec)
makePrecFunc precRules = apply precRules
  where apply       [] s1 s2 = fail s1 s2
        apply (pr:prs) s1 s2 = case pr s1 s2 of
                                 (Just prec) -> prec
                                 Nothing     -> apply prs s1 s2

        fail s1 s2 = (error . concat) [ "Precedence function not defined for:" 
                                      , "\n "
                                      , show s1
                                      , "\n "
                                      , show s2
                                      ]
