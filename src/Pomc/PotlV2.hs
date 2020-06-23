{- |
   Module      : Pomc.PotlV2
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.PotlV2 ( -- * POTL V2 types
                     Dir(..)
                   , Prop(..)
                   , Formula(..)
                   ) where

import Pomc.Check (Checkable(..))
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import qualified Pomc.RPotl as RP (Formula(..))

import qualified Data.Set as S

data Dir = Up | Down deriving (Eq, Ord, Show)

data Formula a = T
               | Atomic (Prop a)
               | Not    (Formula a)
               | Or      (Formula a) (Formula a)
               | And     (Formula a) (Formula a)
               | Xor     (Formula a) (Formula a)
               | Implies (Formula a) (Formula a)
               | Iff     (Formula a) (Formula a)
               | PNext  Dir (Formula a)
               | PBack  Dir (Formula a)
               | XNext  Dir (Formula a)
               | XBack  Dir (Formula a)
               | HNext  Dir (Formula a)
               | HBack  Dir (Formula a)
               | Until  Dir (Formula a) (Formula a)
               | Since  Dir (Formula a) (Formula a)
               | HUntil Dir (Formula a) (Formula a)
               | HSince Dir (Formula a) (Formula a)
               | Eventually (Formula a)
               | Always     (Formula a)
               deriving (Eq, Ord)

instance Checkable (Formula) where
  toReducedPotl f =
    case f of
      T               -> RP.T
      Atomic (Prop p) -> RP.Atomic (Prop p)
      Not g           -> RP.Not (trp g)
      And g h         -> RP.And (trp g) (trp h)
      Or g h          -> RP.Or (trp g) (trp h)
      Xor g h         -> trp $ (g `And` Not h) `Or` (h `And` Not g)
      Implies g h     -> trp $ (Not g) `Or` h
      Iff g h         -> trp $ (g `Implies` h) `And` (h `Implies` g)
      PNext Down g    -> RP.PrecNext  (S.fromList [Yield, Equal]) (trp g)
      PNext Up   g    -> RP.PrecNext  (S.fromList [Equal, Take])  (trp g)
      PBack Down g    -> RP.PrecBack  (S.fromList [Yield, Equal]) (trp g)
      PBack Up   g    -> RP.PrecBack  (S.fromList [Equal, Take])  (trp g)
      XNext Down g    -> RP.ChainNext (S.fromList [Yield, Equal]) (trp g)
      XNext Up   g    -> RP.ChainNext (S.fromList [Equal, Take])  (trp g)
      XBack Down g    -> RP.ChainBack (S.fromList [Yield, Equal]) (trp g)
      XBack Up   g    -> RP.ChainBack (S.fromList [Equal, Take])  (trp g)
      HNext Down g    -> RP.HierNextTake  (trp g)
      HNext Up   g    -> RP.HierNextYield (trp g)
      HBack Down g    -> RP.HierBackTake  (trp g)
      HBack Up   g    -> RP.HierBackYield (trp g)
      Until Down g h  -> RP.Until (S.fromList [Yield, Equal]) (trp g) (trp h)
      Until Up   g h  -> RP.Until (S.fromList [Equal, Take])  (trp g) (trp h)
      Since Down g h  -> RP.Since (S.fromList [Yield, Equal]) (trp g) (trp h)
      Since Up   g h  -> RP.Since (S.fromList [Equal, Take])  (trp g) (trp h)
      HUntil Down g h -> RP.HierUntilTake  (trp g) (trp h)
      HUntil Up   g h -> RP.HierUntilYield (trp g) (trp h)
      HSince Down g h -> RP.HierSinceTake  (trp g) (trp h)
      HSince Up   g h -> RP.HierSinceYield (trp g) (trp h)
      Eventually g    -> RP.Eventually' (RP.And (RP.Not . RP.Atomic $ End) (trp g))
      Always g        -> trp . Not . Eventually . Not $ g
    where trp = toReducedPotl

instance (Show a) => Show (Formula a) where
  show f = case f of
             T               -> showp f
             Atomic _        -> showp f
             Not g           -> concat ["~ ", showp g]
             And g h         -> concat [showp g, " And ",  showp h]
             Or g h          -> concat [showp g, " Or ",   showp h]
             Xor g h         -> concat [showp g, " Xor ",  showp h]
             Implies g h     -> concat [showp g, " --> ",  showp h]
             Iff g h         -> concat [showp g, " <--> ", showp h]
             PNext Down g    -> concat ["PNd ", showp g]
             PNext Up   g    -> concat ["PNu ", showp g]
             PBack Down g    -> concat ["PBd ", showp g]
             PBack Up   g    -> concat ["PBu ", showp g]
             XNext Down g    -> concat ["XNd ", showp g]
             XNext Up   g    -> concat ["XNu ", showp g]
             XBack Down g    -> concat ["XBd ", showp g]
             XBack Up   g    -> concat ["XBu ", showp g]
             HNext Down g    -> concat ["HNd ", showp g]
             HNext Up   g    -> concat ["HNu ", showp g]
             HBack Down g    -> concat ["HBd ", showp g]
             HBack Up   g    -> concat ["HBu ", showp g]
             Until Down g h  -> concat [showp g, " Ud ",  showp h]
             Until Up   g h  -> concat [showp g, " Uu ",  showp h]
             Since Down g h  -> concat [showp g, " Sd ",  showp h]
             Since Up   g h  -> concat [showp g, " Su ",  showp h]
             HUntil Down g h -> concat [showp g, " HUd ", showp h]
             HUntil Up   g h -> concat [showp g, " HUu ", showp h]
             HSince Down g h -> concat [showp g, " HSd ", showp h]
             HSince Up   g h -> concat [showp g, " HSu ", showp h]
             Eventually g    -> concat ["F ", showp g]
             Always g        -> concat ["G ", showp g]
    where showp T = "T"
          showp (Atomic (Prop p)) = show p
          showp (Atomic End) = "#"
          showp f = concat ["(", show f, ")"]

instance Functor Formula where
  fmap func f = case f of
                  T               -> T
                  Atomic p        -> Atomic (fmap func p)
                  Not g           -> Not (fmap func g)
                  And     g h     -> And     (fmap func g) (fmap func h)
                  Or      g h     -> Or      (fmap func g) (fmap func h)
                  Xor     g h     -> Xor     (fmap func g) (fmap func h)
                  Implies g h     -> Implies (fmap func g) (fmap func h)
                  Iff     g h     -> Iff     (fmap func g) (fmap func h)
                  PNext Down g    -> PNext Down (fmap func g)
                  PNext Up   g    -> PNext Up   (fmap func g)
                  PBack Down g    -> PBack Down (fmap func g)
                  PBack Up   g    -> PBack Up   (fmap func g)
                  XNext Down g    -> XNext Down (fmap func g)
                  XNext Up   g    -> XNext Up   (fmap func g)
                  XBack Down g    -> XBack Down (fmap func g)
                  XBack Up   g    -> XBack Up   (fmap func g)
                  HNext Down g    -> HNext Down (fmap func g)
                  HNext Up   g    -> HNext Up   (fmap func g)
                  HBack Down g    -> HBack Down (fmap func g)
                  HBack Up   g    -> HBack Up   (fmap func g)
                  Until Down g h  -> Until Down (fmap func g) (fmap func h)
                  Until Up   g h  -> Until Up   (fmap func g) (fmap func h)
                  Since Down g h  -> Since Down (fmap func g) (fmap func h)
                  Since Up   g h  -> Since Up   (fmap func g) (fmap func h)
                  HUntil Down g h -> HUntil Down (fmap func g) (fmap func h)
                  HUntil Up   g h -> HUntil Up   (fmap func g) (fmap func h)
                  HSince Down g h -> HSince Down (fmap func g) (fmap func h)
                  HSince Up   g h -> HSince Up   (fmap func g) (fmap func h)
                  Eventually g    -> Eventually (fmap func g)
                  Always g        -> Always (fmap func g)
