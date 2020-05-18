module POMC.PotlV2 ( Dir(..)
                   , Prop(..)
                   , Formula(..)
                   ) where

import POMC.Check (Checkable(..))
import POMC.Opa (Prec(..))
import qualified POMC.RPotl as RP (Formula(..), Prop(..))

import qualified Data.Set as S

data Dir = Up | Down deriving (Eq, Ord, Show)

data Prop a = Prop a deriving (Eq, Ord, Show)

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
               deriving (Eq, Ord, Show)

instance Checkable (Formula) where
  toReducedPotl f =
    case f of
      T               -> RP.T
      Atomic (Prop p) -> RP.Atomic (RP.Prop p)
      Not g           -> RP.Not (trp g)
      Or g h          -> RP.Or (trp g) (trp h)
      And g h         -> RP.And (trp g) (trp h)
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
      HNext Down g    -> RP.HierNextYield (trp g)
      HNext Up   g    -> RP.HierNextTake  (trp g)
      HBack Down g    -> RP.HierBackYield (trp g)
      HBack Up   g    -> RP.HierBackTake  (trp g)
      Until Down g h  -> RP.Until (S.fromList [Yield, Equal]) (trp g) (trp h)
      Until Up   g h  -> RP.Until (S.fromList [Equal, Take])  (trp g) (trp h)
      Since Down g h  -> RP.Since (S.fromList [Yield, Equal]) (trp g) (trp h)
      Since Up   g h  -> RP.Since (S.fromList [Equal, Take])  (trp g) (trp h)
      HUntil Down g h -> RP.HierUntilYield (trp g) (trp h)
      HUntil Up   g h -> RP.HierUntilTake  (trp g) (trp h)
      HSince Down g h -> RP.HierSinceYield (trp g) (trp h)
      HSince Up   g h -> RP.HierSinceTake  (trp g) (trp h)
      Eventually g    -> RP.Eventually' (RP.And (RP.Not . RP.Atomic $ RP.End) (trp g))
      Always g        -> trp . Not . Eventually . Not $ g
    where trp = toReducedPotl
