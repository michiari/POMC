{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.State
   Copyright   : 2021 Francesco Pontiggia
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
import Pomc.PropConv (APType)
import Pomc.Potl (negative)

import Data.Set (Set)
import qualified Data.Set as S
import GHC.Generics (Generic)
import Data.Hashable

import Control.DeepSeq (NFData(..), deepseq)

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

-- to allow parallelism
instance NFData State where
  rnf (FState curr pend _ _ _) = curr `deepseq` pend `deepseq` ()
  rnf (WState curr pend instack _ _ _) = curr `deepseq` pend `deepseq` instack `deepseq` ()

showPendCombs :: Set (EncodedSet, Bool, Bool, Bool) -> String
showPendCombs = unlines . map show . S.toList

showFormulaSet :: (Show a) => (APType -> a) -> FormulaSet -> String
showFormulaSet transAP fset =
  let fs = S.toList fset
      posfs = filter (not . negative) fs
      negfs = filter (negative) fs
  in show $ map (fmap transAP) (posfs ++ negfs)

showAtom :: (Show a) => BitEncoding -> (APType -> a) -> Atom -> String
showAtom bitenc transAP atom =
  "FS: " ++ showFormulaSet transAP (E.decode bitenc atom) ++ "\t\tES: " ++ show atom

showState :: (Show a) => BitEncoding -> (APType -> a) -> State -> String
showState bitenc transAP (FState c p xl xe xr) =
  "{ C: "    ++ showAtom bitenc transAP c  ++
  "\n, P: "  ++ showAtom bitenc transAP p  ++
  "\n, XL: " ++ show xl                    ++
  "\n, X=: " ++ show xe                    ++
  "\n, XR: " ++ show xr                    ++
  "\n}"
showState bitenc transAP (WState c p st xl xe xr) =
  "{ C: "    ++ showAtom bitenc transAP c  ++
  "\n, P: "  ++ showAtom bitenc transAP p  ++
  "\n, ST: " ++ showAtom bitenc transAP st ++
  "\n, XL: " ++ show xl                    ++
  "\n, X=: " ++ show xe                    ++
  "\n, XR: " ++ show xr                    ++
  "\n}"
