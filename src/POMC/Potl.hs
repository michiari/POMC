module POMC.Potl ( Formula(..)
                 , ExtFormula(..)
                 , Prop(..)
                 , negation
                 ) where

import POMC.Opa

import Data.Set (Set)

data Prop a = Prop a deriving (Eq, Ord, Show)

data Formula a = Atomic    (Prop a)
               | Not       (Formula a)
               | Or        (Formula a) (Formula a)
               | And       (Formula a) (Formula a)
               | PrecNext  (Set Prec) (Formula a)
               | PrecBack  (Set Prec) (Formula a)
               | ChainNext (Set Prec) (Formula a)
               | ChainBack (Set Prec) (Formula a)
               | Until     (Set Prec) (Formula a) (Formula a)
               | Since     (Set Prec) (Formula a) (Formula a)
               | HierNext  (Set Prec) (Formula a)
               | HierBack  (Set Prec) (Formula a)
               | HierUntil (Set Prec) (Formula a) (Formula a)
               | HierSince (Set Prec) (Formula a) (Formula a)
               deriving (Eq, Ord, Show)

data ExtFormula a = Normal     (Formula a)
                  | Xor        (Formula a) (Formula a)
                  | Implies    (Formula a) (Formula a)
                  | Iff        (Formula a) (Formula a)
                  | Globally   (Formula a)
                  | Eventually (Formula a)
                  deriving (Eq, Ord, Show)

-- data Pi = YET | YE | YT | Y | ET | E | T
-- data Mi = YT | Y | T

negation :: Formula a -> Formula a
negation (Not f) = f
negation f = Not f
