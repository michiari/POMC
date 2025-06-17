{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.State
   Copyright   : 2021-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.State ( State(..)
                  , Input
                  , Atom
                  , showState
                  , showFormulaSet
                  , showAtom
                  , showPendCombs
                  ) where

import Pomc.Encoding (EncodedSet, FormulaSet, BitEncoding)
import qualified Pomc.Encoding as E
import Pomc.PropConv (PropConv(..))
import Pomc.Potl (negative)

import Data.Set (Set)
import qualified Data.Set as S
import GHC.Generics (Generic)
import Data.Hashable

type Input = EncodedSet
type Atom = EncodedSet

-- a OPA state for both the finite and the infinite case
data State = FState
  { current    :: Atom -- Bit Vector representing the formulas and AP holding in this state
  , pending    :: EncodedSet -- Bit Vector representing temporal obligations holding in the current state
  , mustPush   :: !Bool
  , mustShift  :: !Bool
  , afterPop   :: !Bool
} | WState
  { current    :: Atom -- Bit Vector representing the formulas and AP holding in this state
  , pending    :: EncodedSet -- Bit Vector representing temporal obligations holding in the current state
  , stack      :: EncodedSet -- Bit Vector representing instack temporal obligations holding in current state
  , mustPush   :: !Bool
  , mustShift  :: !Bool
  , afterPop   :: !Bool
} deriving (Generic, Ord, Eq)

instance Hashable State

instance Show State where
  show (FState c p xl xe xr) = "\n{ C: "  ++ show c  ++
                              "\n, P: "  ++ show p  ++
                              "\n, XL: " ++ show xl ++
                              "\n, X=: " ++ show xe ++
                              "\n, XR: " ++ show xr ++
                              "\n}"
  show (WState c p s xl xe xr) = "\n{ C: "  ++ show c  ++
                                "\n, P: "  ++ show p  ++
                                "\n, S: "  ++ show s  ++
                                "\n, XL: " ++ show xl ++
                                "\n, X=: " ++ show xe ++
                                "\n, XR: " ++ show xr ++
                                "\n}"

showPendCombs :: Set (EncodedSet, Bool, Bool, Bool) -> String
showPendCombs = unlines . map show . S.toList

showFormulaSet :: (Show a) => PropConv a -> FormulaSet -> String
showFormulaSet pconv fset =
  let fs = S.toList fset
      posfs = filter (not . negative) fs
      negfs = filter (negative) fs
  in show $ map (fmap $ decodeAP pconv) (posfs ++ negfs)

showAtom :: (Show a) => BitEncoding -> PropConv a -> Atom -> String
showAtom bitenc pconv atom =
  "FS: " ++ showFormulaSet pconv (E.decode bitenc atom) ++ "\t\tES: " ++ show atom

showState :: (Show a) => BitEncoding -> PropConv a -> State -> String
showState bitenc pconv (FState c p xl xe xr) =
  "{ C: "    ++ showAtom bitenc pconv c  ++
  "\n, P: "  ++ showAtom bitenc pconv p  ++
  "\n, XL: " ++ show xl                    ++
  "\n, X=: " ++ show xe                    ++
  "\n, XR: " ++ show xr                    ++
  "\n}"
showState bitenc pconv (WState c p st xl xe xr) =
  "{ C: "    ++ showAtom bitenc pconv c  ++
  "\n, P: "  ++ showAtom bitenc pconv p  ++
  "\n, ST: " ++ showAtom bitenc pconv st ++
  "\n, XL: " ++ show xl                    ++
  "\n, X=: " ++ show xe                    ++
  "\n, XR: " ++ show xr                    ++
  "\n}"
