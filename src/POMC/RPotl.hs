{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module POMC.RPotl ( -- Main data types
                    Formula(..)
                  , Prop(..)
                    -- Predicates on formulas
                  , atomic
                  , future
                  , negative
                    -- Operations on formulas
                  , formulaAt
                  , negation
                  , normalize
                  ) where

import POMC.Opa (Prec(..))

import Data.Set (Set)
import qualified Data.Set as S

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

data Prop a = Prop a deriving (Eq, Ord, Show, Generic, NFData)

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
               | Eventually (Formula a)
               deriving (Eq, Ord, Generic, NFData)

instance (Show a) => Show (Formula a) where
  show T                    = "T"
  show (Atomic (Prop p))    = show p
  show (Not a@(Atomic _))   = "~" ++ show a
  show (Not g)              = "~(" ++ show g ++ ")"
  show (Or g h)             = "(" ++ show g ++ ")Or(" ++ show h ++ ")"
  show (And g h)            = "(" ++ show g ++ ")And(" ++ show h ++ ")"
  show (PrecNext ps g)      = "N" ++ showps ps ++ "(" ++ show g ++ ")"
  show (PrecBack ps g)      = "B" ++ showps ps ++ "(" ++ show g ++ ")"
  show (ChainNext ps g)     = "Xf" ++ showps ps ++ "(" ++ show g ++ ")"
  show (ChainBack ps g)     = "Xp" ++ showps ps ++ "(" ++ show g ++ ")"
  show (Until ps g h)       = "(" ++ show g ++ ")U" ++ showps ps ++ "(" ++ show h ++ ")"
  show (Since ps g h)       = "(" ++ show g ++ ")S" ++ showps ps ++ "(" ++ show h ++ ")"
  show (HierNextYield g)    = "HN[" ++ show Yield ++ "](" ++ show g ++ ")"
  show (HierBackYield g)    = "HB[" ++ show Yield ++ "](" ++ show g ++ ")"
  show (HierNextTake  g)    = "HN[" ++ show Take  ++ "](" ++ show g ++ ")"
  show (HierBackTake  g)    = "HB[" ++ show Take  ++ "](" ++ show g ++ ")"
  show (HierUntilYield g h) = "(" ++ show g ++ ")HU[" ++ show Yield ++ "](" ++ show h ++ ")"
  show (HierSinceYield g h) = "(" ++ show g ++ ")HS[" ++ show Yield ++ "](" ++ show h ++ ")"
  show (HierUntilTake  g h) = "(" ++ show g ++ ")HU[" ++ show Take  ++ "](" ++ show h ++ ")"
  show (HierSinceTake  g h) = "(" ++ show g ++ ")HS[" ++ show Take  ++ "](" ++ show h ++ ")"
  show (HierTakeHelper g)   = "Xp<'" ++ "(" ++ show g ++ ")"
  show (Eventually g)       = "F" ++ "(" ++ show g ++ ")"

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
--future (Eventually     {}) = True
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
                Eventually g       -> Eventually (normalize g)
