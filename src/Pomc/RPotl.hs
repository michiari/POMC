{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.RPotl
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.RPotl ( -- * RPOTL type
                    Formula(..)
                    -- * Predicates on formulas
                  , atomic
                  , future
                  , negative
                    -- * Operations on formulas
                  , formulaAt
                  , negation
                  , normalize
                  ) where

import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))

import Data.Set (Set)
import qualified Data.Set as S

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

data Formula a = T
               | Atomic (Prop a)
               | Not (Formula a)
               | Or  (Formula a) (Formula a)
               | And (Formula a) (Formula a)
               | PrecNext  (Set Prec) (Formula a)
               | PrecBack  (Set Prec) (Formula a)
               | ChainNext (Set Prec) (Formula a)
               | ChainBack (Set Prec) (Formula a)
               | Until (Set Prec) (Formula a) (Formula a)
               | Since (Set Prec) (Formula a) (Formula a)
               | HierNextYield (Formula a)
               | HierBackYield (Formula a)
               | HierNextTake  (Formula a)
               | HierBackTake  (Formula a)
               | HierUntilYield (Formula a) (Formula a)
               | HierSinceYield (Formula a) (Formula a)
               | HierUntilTake  (Formula a) (Formula a)
               | HierSinceTake  (Formula a) (Formula a)
               | HierTakeHelper (Formula a)
               | Eventually' (Formula a)
               deriving (Eq, Ord, Generic, NFData)

instance (Show a) => Show (Formula a) where
  show f = case f of
             T                  -> showp f
             Atomic _           -> showp f
             Not g              -> concat ["~", showp g]
             And g h            -> concat [showp g, " And ", showp h]
             Or g h             -> concat [showp g,  " Or ", showp h]
             PrecNext ps g      -> concat ["PN", showps ps, " ", showp g]
             PrecBack ps g      -> concat ["PB", showps ps, " ", showp g]
             ChainNext ps g     -> concat ["XN", showps ps, " ", showp g]
             ChainBack ps g     -> concat ["XB", showps ps, " ", showp g]
             Until ps g h       -> concat [showp g, " U", showps ps,  " ", showp h]
             Since ps g h       -> concat [showp g, " S", showps ps,  " ", showp h]
             HierNextYield g    -> concat ["HN[", show Yield, "] ", showp g]
             HierBackYield g    -> concat ["HB[", show Yield, "] ", showp g]
             HierNextTake  g    -> concat ["HN[",  show Take, "] ", showp g]
             HierBackTake  g    -> concat ["HB[",  show Take, "] ", showp g]
             HierUntilYield g h -> concat [showp g, " HU[" , show Yield, "] ", showp h]
             HierSinceYield g h -> concat [showp g, " HS[" , show Yield, "] ", showp h]
             HierUntilTake  g h -> concat [showp g, " HU[" ,  show Take, "] ", showp h]
             HierSinceTake  g h -> concat [showp g, " HS[" ,  show Take, "] ", showp h]
             HierTakeHelper g   -> concat ["Xp<' ", showp g]
             Eventually' g      -> concat ["F ", showp g]
    where showp T = "T"
          showp (Atomic (Prop p)) = show p
          showp (Atomic End)      = "#"
          showp f = concat ["(", show f, ")"]

atomic :: Formula a -> Bool
atomic (Atomic _) = True
atomic _ = False

future :: Formula a -> Bool
future (PrecNext       {}) = True
future (ChainNext      {}) = True
future (Until          {}) = True
future (HierNextYield  {}) = True
future (HierNextTake   {}) = True
future (HierUntilYield {}) = True
future (HierUntilTake  {}) = True
future (HierTakeHelper {}) = True
future (Eventually'    {}) = True
future _ = False

negative :: Formula a -> Bool
negative (Not f) = True
negative f = False

formulaAt :: Integral n => n -> Formula a -> Formula a
formulaAt n f
  | n <= 1    = f
  | otherwise = formulaAt (n-1) (PrecNext (S.fromList [Yield, Equal, Take]) f)

showps pset = "[" ++ concat (map show (S.toList pset)) ++ "]"

negation :: Formula a -> Formula a
negation (Not f) = f
negation f = Not f

normalize f = case f of
                T                  -> f
                Atomic p           -> f
                Not (Not g)        -> normalize g    -- remove double negation
                Not g              -> Not (normalize g)
                Or g h             -> Or  (normalize g) (normalize h)
                And g h            -> And (normalize g) (normalize h)
                PrecNext pset g    -> PrecNext pset (normalize g)
                PrecBack pset g    -> PrecBack pset (normalize g)
                ChainNext pset g   -> ChainNext pset (normalize g)
                ChainBack pset g   -> ChainBack pset (normalize g)
                Until pset g h     -> Until pset (normalize g) (normalize h)
                Since pset g h     -> Since pset (normalize g) (normalize h)
                HierNextYield g    -> HierNextYield (normalize g)
                HierBackYield g    -> HierBackYield (normalize g)
                HierNextTake  g    -> HierNextTake  (normalize g)
                HierBackTake  g    -> HierBackTake  (normalize g)
                HierUntilYield g h -> HierUntilYield (normalize g) (normalize h)
                HierSinceYield g h -> HierSinceYield (normalize g) (normalize h)
                HierUntilTake  g h -> HierUntilTake  (normalize g) (normalize h)
                HierSinceTake  g h -> HierSinceTake  (normalize g) (normalize h)
                HierTakeHelper g   -> HierTakeHelper (normalize g)
                Eventually' g      -> Eventually' (normalize g)
