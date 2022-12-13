{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Potl
   Copyright   : 2020-2021 Davide Bergamaschi, Michele Chiari and Francesco Pontiggia
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Potl ( Dir(..)
                 , Prop(..)
                 , Formula(..)
                 , getProps
                   -- * Predicates on formulas
                 , atomic
                 , future
                 , negative
                   -- * Operations on formulas
                 , negation
                 , normalize
                 , pnf
                 , formulaAt
                 , formulaAfter
                 , formulaAtDown
                 , formulaAtUp
                 ) where

import Pomc.Prop (Prop(..))
import Data.List (nub, uncons)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData(..))

import Data.Hashable

data Dir = Up | Down deriving (Eq, Ord, Show, Generic)

data Formula a =
  -- Propositional
  T
  | Atomic  (Prop a)
  | Not     (Formula a)
  | Or      (Formula a) (Formula a)
  | And     (Formula a) (Formula a)
  | Xor     (Formula a) (Formula a)
  | Implies (Formula a) (Formula a)
  | Iff     (Formula a) (Formula a)
  -- POTL
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
  -- Weak POTL
  | WPNext    Dir (Formula a)
  -- | WPBack    Dir (Formula a)
  | WXNext    Dir (Formula a)
  -- | WXBack    Dir (Formula a)
  -- | WHNext    Dir (Formula a)
  -- | WHBack    Dir (Formula a)
  | Release   Dir (Formula a) (Formula a)
  -- | PRelease  Dir (Formula a) (Formula a)
  -- | HRelease  Dir (Formula a) (Formula a)
  -- | HPRelease Dir (Formula a) (Formula a)
  -- LTL
  | Eventually (Formula a)
  | Always     (Formula a)
  -- Auxiliary
  | AuxBack Dir (Formula a)  -- AuxBack Up is NEVER used
  deriving (Eq, Ord, Generic)

instance (Show a) => Show (Formula a) where
  show f = case f of
    T                -> showp f
    Atomic _         -> showp f
    Not g            -> concat ["~ ", showp g]
    And g h          -> concat [showp g, " And ",  showp h]
    Or g h           -> concat [showp g, " Or ",   showp h]
    Xor g h          -> concat [showp g, " Xor ",  showp h]
    Implies g h      -> concat [showp g, " --> ",  showp h]
    Iff g h          -> concat [showp g, " <--> ", showp h]
    PNext Down g     -> concat ["PNd ", showp g]
    PNext Up   g     -> concat ["PNu ", showp g]
    PBack Down g     -> concat ["PBd ", showp g]
    PBack Up   g     -> concat ["PBu ", showp g]
    XNext Down g     -> concat ["XNd ", showp g]
    XNext Up   g     -> concat ["XNu ", showp g]
    XBack Down g     -> concat ["XBd ", showp g]
    XBack Up   g     -> concat ["XBu ", showp g]
    HNext Down g     -> concat ["HNd ", showp g]
    HNext Up   g     -> concat ["HNu ", showp g]
    HBack Down g     -> concat ["HBd ", showp g]
    HBack Up   g     -> concat ["HBu ", showp g]
    Until Down g h   -> concat [showp g, " Ud ",  showp h]
    Until Up   g h   -> concat [showp g, " Uu ",  showp h]
    Since Down g h   -> concat [showp g, " Sd ",  showp h]
    Since Up   g h   -> concat [showp g, " Su ",  showp h]
    HUntil Down g h  -> concat [showp g, " HUd ", showp h]
    HUntil Up   g h  -> concat [showp g, " HUu ", showp h]
    HSince Down g h  -> concat [showp g, " HSd ", showp h]
    HSince Up   g h  -> concat [showp g, " HSu ", showp h]
    WPNext Up   g    -> concat ["WPNu ", showp g]
    WPNext Down g    -> concat ["WPNd ", showp g]
    WXNext Up   g    -> concat ["WXNu ", showp g]
    WXNext Down g    -> concat ["WXNd ", showp g]
    Release Down g h -> concat [showp g, " Rd ", showp h]
    Release Up   g h -> concat [showp g, " Ru ", showp h]
    Eventually g     -> concat ["F ", showp g]
    Always g         -> concat ["G ", showp g]
    AuxBack Down g   -> concat ["AuxBd ", showp g]
    AuxBack Up g     -> concat ["AuxBu ", showp g]
    where showp T = "T"
          showp (Atomic (Prop p)) = show p
          showp (Atomic End) = "#"
          showp g = concat ["(", show g, ")"]

instance Hashable Dir
instance Hashable a => Hashable (Formula a)

instance NFData (Formula a) where
  rnf formula = formula `seq` ()

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
    PNext dir g     -> PNext dir (fmap func g)
    PBack dir g     -> PBack dir (fmap func g)
    XNext dir g     -> XNext dir (fmap func g)
    XBack dir g     -> XBack dir (fmap func g)
    HNext dir g     -> HNext dir (fmap func g)
    HBack dir g     -> HBack dir (fmap func g)
    Until dir g h   -> Until dir (fmap func g) (fmap func h)
    Since dir g h   -> Since dir (fmap func g) (fmap func h)
    HUntil dir g h  -> HUntil dir (fmap func g) (fmap func h)
    HSince dir g h  -> HSince dir (fmap func g) (fmap func h)
    WPNext dir g    -> WPNext dir (fmap func g)
    WXNext dir g    -> WXNext dir (fmap func g)
    Release dir g h -> Release dir (fmap func g) (fmap func h)
    Eventually g    -> Eventually (fmap func g)
    Always g        -> Always (fmap func g)
    AuxBack dir g   -> AuxBack dir (fmap func g)


--get all the atomic propositions used by a formula, removing duplicates
getProps :: (Eq a) => Formula a -> [Prop a]
getProps formula = nub $ collectProps formula
  where collectProps f = case f of
          T                  -> []
          Atomic p           -> [p]
          Not g              -> getProps g
          Or g h             -> getProps g ++ getProps h
          And g h            -> getProps g ++ getProps h
          Xor g h            -> getProps g ++ getProps h
          Implies g h        -> getProps g ++ getProps h
          Iff g h            -> getProps g ++ getProps h
          PNext _ g          -> getProps g
          PBack _ g          -> getProps g
          XNext _ g          -> getProps g
          XBack _ g          -> getProps g
          HNext _ g          -> getProps g
          HBack _ g          -> getProps g
          Until _ g h        -> getProps g ++ getProps h
          Since _ g h        -> getProps g ++ getProps h
          HUntil _ g h       -> getProps g ++ getProps h
          HSince _ g h       -> getProps g ++ getProps h
          WPNext _ g         -> getProps g
          WXNext _ g         -> getProps g
          Release _ g h      -> getProps g ++ getProps h
          Eventually g       -> getProps g
          Always g           -> getProps g
          AuxBack _ g        -> getProps g

atomic :: Formula a -> Bool
atomic (Atomic _) = True
atomic _ = False

future :: Formula a -> Bool
future (PNext      {})      = True
future (XNext      {})      = True
future (HNext      {})      = True
future (Until      {})      = True
future (HUntil     {})      = True
future (WPNext     {})      = True
future (WXNext     {})      = True
future (Release    {})      = True
future (Eventually {})      = True
future _ = False

negative :: Formula a -> Bool
negative (Not _) = True
negative _ = False

formulaAt :: Int -> Formula a -> Formula a
formulaAt n f
  | n <= 1    = f
  | otherwise = formulaAt (n-1) (Or (PNext Up f) (PNext Down f))

formulaAfter ::  [Dir] -> Formula a ->  Formula a
formulaAfter  l f = case uncons l of
    Nothing -> f
    Just (dir, dirs) -> PNext dir (formulaAfter dirs f)

formulaAtDown :: Int -> Formula a -> Formula a
formulaAtDown n f
  | n <= 1         = f
  | otherwise = formulaAtDown (n-1) (PNext Down f)

formulaAtUp :: Int -> Formula a -> Formula a
formulaAtUp n f
  | n <= 1         = f
  | otherwise = formulaAtDown (n-1) (PNext Up f)


negation :: Formula a -> Formula a
negation (Not f) = f
negation f = Not f

-- remove double negation
normalize :: Formula a -> Formula a
normalize f = case f of
  T                  -> f
  Atomic _           -> f
  Not (Not g)        -> normalize g
  Not (Always g)     -> Eventually . normalize . Not $ g
  Not g              -> Not (normalize g)
  Or g h             -> Or  (normalize g) (normalize h)
  And g h            -> And (normalize g) (normalize h)
  Xor g h            -> Xor (normalize g) (normalize h)
  Implies g h        -> Implies (normalize g) (normalize h)
  Iff g h            -> Iff (normalize g) (normalize h)
  PNext dir g        -> PNext dir (normalize g)
  PBack dir g        -> PBack dir (normalize g)
  XNext dir g        -> XNext dir (normalize g)
  XBack dir g        -> XBack dir (normalize g)
  HNext dir g        -> HNext dir (normalize g)
  HBack dir g        -> HBack dir (normalize g)
  Until dir g h      -> Until dir (normalize g) (normalize h)
  Since dir g h      -> Since dir (normalize g) (normalize h)
  HUntil dir g h     -> HUntil dir (normalize g) (normalize h)
  HSince dir g h     -> HSince dir (normalize g) (normalize h)
  WPNext dir g       -> WPNext dir (normalize g)
  WXNext dir g       -> WXNext dir (normalize g)
  Release dir g h    -> Release dir (normalize g) (normalize h)
  Eventually g       -> Eventually (normalize g)
  Always g           -> Not . Eventually . normalize . Not $ g
  AuxBack dir g      -> AuxBack dir (normalize g)

-- to positive normal form
pnf :: Formula a -> Formula a
pnf f = case f of
  -- Positive operators
  T                  -> f
  Atomic _           -> f
  Or g h             -> Or  (pnf g) (pnf h)
  And g h            -> And (pnf g) (pnf h)
  Xor g h            -> Xor (pnf g) (pnf h)
  Implies g h        -> Implies (pnf g) (pnf h)
  Iff g h            -> Iff (pnf g) (pnf h)
  PNext dir g        -> PNext dir (pnf g)
  PBack dir g        -> PBack dir (pnf g)
  XNext dir g        -> XNext dir (pnf g)
  XBack dir g        -> XBack dir (pnf g)
  HNext dir g        -> HNext dir (pnf g)
  HBack dir g        -> HBack dir (pnf g)
  Until dir g h      -> Until dir (pnf g) (pnf h)
  Since dir g h      -> Since dir (pnf g) (pnf h)
  HUntil dir g h     -> HUntil dir (pnf g) (pnf h)
  HSince dir g h     -> HSince dir (pnf g) (pnf h)
  WPNext dir g       -> WPNext dir (pnf g)
  WXNext dir g       -> WXNext dir (pnf g)
  Release dir g h    -> Release dir (pnf g) (pnf h)
  Eventually g       -> Eventually (pnf g)
  Always g           -> Always (pnf g)
  AuxBack dir g      -> AuxBack dir (pnf g)
  -- Negated operators
  Not T                 -> f
  Not (Atomic _)        -> f
  Not (Not g)           -> pnf g
  Not (Or g h)          -> And (pnf $ Not g) (pnf $ Not h)
  Not (And g h)         -> Or (pnf $ Not g) (pnf $ Not h)
  Not (Xor g h)         -> Iff (pnf g) (pnf h)
  Not (Implies g h)     -> And (pnf g) (pnf $ Not h)
  Not (Iff g h)         -> Xor (pnf g) (pnf h)
  Not (PNext dir g)     -> WPNext dir (pnf $ Not g)
  Not (PBack _dir _g)     -> error "Past weak operators not supported yet." -- WPBack dir (pnf $ Not g)
  Not (XNext dir g)     -> WXNext dir (pnf $ Not g)
  Not (XBack _dir _g)     -> error "Past weak operators not supported yet." -- WXBack dir (pnf $ Not g)
  Not (HNext _dir _g)     -> error "Hierarchical weak operators not supported yet." -- WHNext dir (pnf $ Not g)
  Not (HBack _dir _g)     -> error "Hierarchical weak operators not supported yet." -- HBack dir (pnf $ Not g)
  Not (Until dir g h)   -> Release dir (pnf $ Not g) (pnf $ Not h)
  Not (Since _dir _g _h)   -> error "Past weak operators not supported yet." -- PRelease dir (pnf $ Not g) (pnf $ Not h)
  Not (HUntil _dir _g _h)  -> error "Hierarchical weak operators not supported yet." -- HRelease dir (pnf $ Not g) (pnf $ Not h)
  Not (HSince _dir _g _h)  -> error "Hierarchical weak operators not supported yet." -- HPRelease dir (pnf $ Not g) (pnf $ Not h)
  Not (WPNext dir g)    -> PNext dir (pnf $ Not g)
  Not (WXNext dir g)    -> XNext dir (pnf $ Not g)
  Not (Release dir g h) -> Release dir (pnf $ Not g) (pnf $ Not h)
  Not (Eventually g)    -> Always (pnf $ Not g)
  Not (Always g)        -> Eventually (pnf $ Not g)
  Not (AuxBack _dir _g)   -> error "Negated auxiliary operators cannot be normalized."
