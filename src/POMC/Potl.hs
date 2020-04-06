module POMC.Potl ( Formula(..)
                 , ExtFormula(..)
                 , Prop(..)
                 , negative
                 , negation
                 , atomic
                 , future
                 , formulaAt
                 , normalize
                 ) where

import POMC.Opa (Prec(..))

import Data.Set (Set)
import qualified Data.Set as S

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
               deriving (Eq, Ord)

data ExtFormula a = Normal     (Formula a)
                  | Xor        (Formula a) (Formula a)
                  | Implies    (Formula a) (Formula a)
                  | Iff        (Formula a) (Formula a)
                  | Globally   (Formula a)
                  | Eventually (Formula a)
                  deriving (Eq, Ord, Show)

-- data Pi = YET | YE | YT | Y | ET | E | T
-- data Mi = YT | Y | T

instance (Show a) => Show (Formula a) where
  show (Atomic (Prop p))  = show p
  show (Not a@(Atomic _)) = "~" ++ show a
  show (Not f)            = "~(" ++ show f ++ ")"
  show (Or g h)           = "(" ++ show g ++ ")Or(" ++ show h ++ ")"
  show (And g h)          = "(" ++ show g ++ ")And(" ++ show h ++ ")"
  show (PrecNext ps g)    = "N" ++ showps ps ++ "(" ++ show g ++ ")"
  show (PrecBack ps g)    = "B" ++ showps ps ++ "(" ++ show g ++ ")"
  show (ChainNext ps g)   = "Xf" ++ showps ps ++ "(" ++ show g ++ ")"
  show (ChainBack ps g)   = "Xp" ++ showps ps ++ "(" ++ show g ++ ")"
  show (Until ps g h)     = "(" ++ show g ++ ")U" ++ showps ps ++
                            "(" ++ show h ++ ")"
  show (Since ps g h)     = "(" ++ show g ++ ")S" ++ showps ps ++
                            "(" ++ show h ++ ")"
  show (HierNext ps g)    = "HN" ++ showps ps ++ "(" ++ show g ++ ")"
  show (HierBack ps g)    = "HB" ++ showps ps ++ "(" ++ show g ++ ")"
  show (HierUntil ps g h) = "(" ++ show g ++ ")HU" ++ showps ps ++
                            "(" ++ show h ++ ")"
  show (HierSince ps g h) = "(" ++ show g ++ ")HS" ++ showps ps ++
                            "(" ++ show h ++ ")"

negative :: Formula a -> Bool
negative (Not f) = True
negative f = False

negation :: Formula a -> Formula a
negation (Not f) = f
negation f = Not f

atomic :: Formula a -> Bool
atomic (Atomic _) = True
atomic _ = False

future :: Formula a -> Bool
future (PrecNext  {}) = True
future (ChainNext {}) = True
future (Until     {}) = True
future (HierNext  {}) = True
future (HierUntil {}) = True
future _ = False

formulaAt :: Integral n => n -> Formula a -> Formula a
formulaAt n f
  | n <= 1    = f
  | otherwise = formulaAt (n-1) (PrecNext (S.fromList [Yield, Equal, Take]) f)

showps pset = "[" ++ concat (map show (S.toList pset)) ++ "]"

normalize f = case f of 
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
                HierNext pset g    -> HierNext pset (normalize g)
                HierBack pset g    -> HierBack pset (normalize g)
                HierUntil pset g h -> HierUntil pset (normalize g) (normalize h)
                HierSince pset g h -> HierSince pset (normalize g) (normalize h)
