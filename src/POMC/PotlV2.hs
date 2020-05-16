module POMC.PotlV2 ( Formula(..)
                   , Dir
                   ) where

import POMC.Check (Checkable(..))
import POMC.Opa (Prec(..))
import POMC.Potl (Prop(..))
import qualified POMC.Potl as P (Formula(..))

import qualified Data.Set as S

data Dir = Up | Down deriving (Eq, Ord, Show)

data Formula a = T
               | Atomic (Prop a)
               | Not (Formula a)
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
  toFormula f =
    case f of
      T               -> P.T
      Atomic p        -> P.Atomic p
      Not g           -> P.Not (tf g)
      Or g h          -> P.Or (tf g) (tf h)
      And g h         -> P.And (tf g) (tf h)
      Xor g h         -> tf $ (g `And` Not h) `Or` (h `And` Not g)
      Implies g h     -> tf $ (Not g) `Or` h
      Iff g h         -> tf $ (g `Implies` h) `And` (h `Implies` g)
      PNext Down g    -> P.PrecNext  (S.fromList [Yield, Equal]) (tf g)
      PNext Up   g    -> P.PrecNext  (S.fromList [Equal, Take])  (tf g)
      PBack Down g    -> P.PrecBack  (S.fromList [Yield, Equal]) (tf g)
      PBack Up   g    -> P.PrecBack  (S.fromList [Equal, Take])  (tf g)
      XNext Down g    -> P.ChainNext (S.fromList [Yield, Equal]) (tf g)
      XNext Up   g    -> P.ChainNext (S.fromList [Equal, Take])  (tf g)
      XBack Down g    -> P.ChainBack (S.fromList [Yield, Equal]) (tf g)
      XBack Up   g    -> P.ChainBack (S.fromList [Equal, Take])  (tf g)
      HNext Down g    -> P.HierNextYield (tf g)
      HNext Up   g    -> P.HierNextTake  (tf g)
      HBack Down g    -> P.HierBackYield (tf g)
      HBack Up   g    -> P.HierBackTake  (tf g)
      Until Down g h  -> P.Until (S.fromList [Yield, Equal]) (tf g) (tf h)
      Until Up   g h  -> P.Until (S.fromList [Equal, Take])  (tf g) (tf h)
      Since Down g h  -> P.Since (S.fromList [Yield, Equal]) (tf g) (tf h)
      Since Up   g h  -> P.Since (S.fromList [Equal, Take])  (tf g) (tf h)
      HUntil Down g h -> P.HierUntilYield (tf g) (tf h)
      HUntil Up   g h -> P.HierUntilTake  (tf g) (tf h)
      HSince Down g h -> P.HierSinceYield (tf g) (tf h)
      HSince Up   g h -> P.HierSinceTake  (tf g) (tf h)
      Eventually g    -> P.Eventually (tf g)
      Always g        -> tf . Not . Eventually . Not $ g
    where tf = toFormula
