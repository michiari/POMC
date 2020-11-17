{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.RPotl
   Copyright   : 2020 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.RPotl ( -- * RPOTL type
                    Formula(..)
                  , getProps
                    -- * Predicates on formulas
                  , atomic
                  , future
                  , negative
                    -- * Operations on formulas
                  , formulaAt
                  , negation
                  , normalize
                  ) where

import Pomc.Prec (Prec(..), PrecSet)
import qualified Pomc.Prec as PS (fromList, toList)
import Pomc.Prop (Prop(..))

import Data.List (nub)

import GHC.Generics (Generic)

import Data.Hashable


data Formula a = T
               | Atomic !(Prop a)
               | Not (Formula a)
               | Or  (Formula a) (Formula a)
               | And (Formula a) (Formula a)
               | PrecNext  PrecSet (Formula a)
               | PrecBack  PrecSet (Formula a)
               | ChainNext PrecSet (Formula a)
               | ChainBack PrecSet (Formula a)
               | Until PrecSet (Formula a) (Formula a)
               | Since PrecSet (Formula a) (Formula a)
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
               deriving (Eq, Ord, Generic)

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
          showp g = concat ["(", show g, ")"]



instance Functor Formula where
  fmap f formula = case formula of
    T                  -> T
    Atomic p           -> Atomic $ fmap f p
    Not g              -> Not $ fmap f g
    And g h            -> And (fmap f g) (fmap f h)
    Or g h             -> Or (fmap f g) (fmap f h)
    PrecNext ps g      -> PrecNext ps (fmap f g)
    PrecBack ps g      -> PrecBack ps (fmap f g)
    ChainNext ps g     -> ChainNext ps (fmap f g)
    ChainBack ps g     -> ChainBack ps (fmap f g)
    Until ps g h       -> Until ps (fmap f g) (fmap f h)
    Since ps g h       -> Since ps (fmap f g) (fmap f h)
    HierNextYield g    -> HierNextYield (fmap f g)
    HierBackYield g    -> HierBackYield (fmap f g)
    HierNextTake  g    -> HierNextTake  (fmap f g)
    HierBackTake  g    -> HierBackTake  (fmap f g)
    HierUntilYield g h -> HierUntilYield (fmap f g) (fmap f h)
    HierSinceYield g h -> HierSinceYield (fmap f g) (fmap f h)
    HierUntilTake  g h -> HierUntilTake  (fmap f g) (fmap f h)
    HierSinceTake  g h -> HierSinceTake  (fmap f g) (fmap f h)
    HierTakeHelper g   -> HierTakeHelper (fmap f g)
    Eventually' g      -> Eventually' (fmap f g)

getProps :: (Eq a) => Formula a -> [Prop a]
getProps formula = nub $ collectProps formula
  where collectProps f = case f of
          T                  -> []
          Atomic p           -> [p]
          Not g              -> getProps g
          And g h            -> getProps g ++ getProps h
          Or g h             -> getProps g ++ getProps h
          PrecNext _ g       -> getProps g
          PrecBack _ g       -> getProps g
          ChainNext _ g      -> getProps g
          ChainBack _ g      -> getProps g
          Until _ g h        -> getProps g ++ getProps h
          Since _ g h        -> getProps g ++ getProps h
          HierNextYield g    -> getProps g
          HierBackYield g    -> getProps g
          HierNextTake  g    -> getProps g
          HierBackTake  g    -> getProps g
          HierUntilYield g h -> getProps g ++ getProps h
          HierSinceYield g h -> getProps g ++ getProps h
          HierUntilTake  g h -> getProps g ++ getProps h
          HierSinceTake  g h -> getProps g ++ getProps h
          HierTakeHelper g   -> getProps g
          Eventually' g      -> getProps g

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
negative (Not _) = True
negative _ = False

formulaAt :: Int -> Formula a -> Formula a
formulaAt n f
  | n <= 1    = f
  | otherwise = formulaAt (n-1) (PrecNext (PS.fromList [Yield, Equal, Take]) f)

showps :: PrecSet -> String
showps pset = "[" ++ concat (map show (PS.toList pset)) ++ "]"

negation :: Formula a -> Formula a
negation (Not f) = f
negation f = Not f

normalize :: Formula a -> Formula a
normalize f = case f of
                T                  -> f
                Atomic _           -> f
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
