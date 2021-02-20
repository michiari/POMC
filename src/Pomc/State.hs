{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.State
   Copyright   : 2020 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.State ( 
                    State(..)
                  , Input
                  , Atom
                  , showStates
                  , showFormulaSet
                  , showAtoms
                  , showPendCombs
                  ) where

import Pomc.Data (EncodedSet, FormulaSet, BitEncoding, EncodedAtom(..))
import qualified Pomc.Data as D
import Data.Set (Set)
import qualified Data.Set as S
import GHC.Generics (Generic)
import Data.Hashable
import Data.BitVector (BitVector)
import qualified Data.BitVector as BV
import Pomc.PotlV2 (Formula(..), Dir(..), negative)
import Control.DeepSeq(NFData(..))

type Input = EncodedSet
type Atom = EncodedSet


instance Hashable State
instance Show State where
  show  (FState current pending mustPush mustShift afterPop)  = "\n{ C: "  ++ show current  ++
                                                               "\n, P: "  ++ show pending   ++
                                                               "\n, XL: " ++ show mustPush  ++
                                                               "\n, X=: " ++ show mustShift  ++
                                                               "\n, XR: " ++ show afterPop ++
                                                               "\n}"
  show (WState current pending instack mustPush mustShift afterPop)  = "\n{ C: "  ++ show current  ++
                                                                       "\n, P: "  ++ show pending   ++
                                                                       "\n, S: "  ++ show instack   ++
                                                                       "\n, XL: " ++ show mustPush  ++
                                                                       "\n, X=: " ++ show mustShift  ++
                                                                       "\n, XR: " ++ show afterPop ++
                                                                       "\n}"                                                            


-- a OPA state for the finite case
data State = FState
  { current    :: Atom -- Bit Vector representing the formulas and AP holding in this state
  , pending    :: EncodedSet -- Bit Vector representing temporal obligations holding in the current state
  , mustPush   :: !Bool
  , mustShift  :: !Bool
  , afterPop    :: !Bool
} | WState
  { current    :: Atom -- Bit Vector representing the formulas and AP holding in this state
  , pending    :: EncodedSet -- Bit Vector representing temporal obligations holding in the current state
  , stack      :: EncodedSet -- BitVector representing  instack temporal obligations holding in current state
  , mustPush   :: !Bool
  , mustShift  :: !Bool
  , afterPop    :: !Bool
} deriving (Generic, Ord, Eq)



instance NFData State where
  rnf (FState current pending _ _ _) = current `seq` pending `seq` ()
  rnf (WState current pending stack _ _ _) = current `seq` pending `seq` stack `seq` ()

showStates :: [State] -> String
showStates = unlines . map show

showFormulaSet :: FormulaSet -> String
showFormulaSet fset = let fs = S.toList fset
                          posfs = filter (not . negative) fs
                          negfs = filter (negative) fs
                      in show (posfs ++ negfs)

showAtom :: BitEncoding -> Atom -> String
showAtom bitenc atom = "FS: " ++ showFormulaSet (D.decode bitenc atom) ++ "\t\tES: " ++ show atom

showAtoms :: BitEncoding -> [Atom] -> String
showAtoms bitenc = unlines . map (showAtom bitenc)

showPendCombs :: Set (EncodedSet, Bool, Bool, Bool) -> String
showPendCombs = unlines . map show . S.toList






    