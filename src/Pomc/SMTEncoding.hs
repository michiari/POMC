{-# LANGUAGE GADTs #-}
{- |
   Module      : Pomc.SMTEncoding
   Copyright   : 2020-2022 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.SMTEncoding ( SMTResult(..)
                        , isSatisfiable
                        ) where

import Pomc.Potl (Formula(..), pnf)
import Pomc.Prec (Alphabet)

-- import System.IO (FilePath)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
                  , BoolExpr, EmptyExprBuilderState(..) )
import What4.Interface ( BaseTypeRepr(..), getConfiguration
                       , freshConstant, safeSymbol
                       , orPred )
import What4.Solver (defaultLogData, z3Options, withZ3)
import qualified What4.Solver as W4
import What4.Protocol.SMTLib2 (assume, sessionWriter, runCheckSat)


data SMTResult = Sat | Unsat | Unknown deriving (Eq, Show)

z3executable :: FilePath
z3executable = "z3"

isSatisfiable :: Formula a
              -> Alphabet a
              -> IO (SMTResult)
isSatisfiable phi alphabet = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng
  -- We use z3 for the time being, might try more backends later
  extendConfig z3Options (getConfiguration sym)

  fenc <- encodeFormula sym (pnf phi) alphabet

  withZ3 sym z3executable defaultLogData $ \session -> do
    -- Assume fenc is true
    assume (sessionWriter session) fenc
    runCheckSat session $ \result ->
      case result of
        W4.Sat _ -> return Sat
        W4.Unsat _ -> return Unsat
        W4.Unknown -> return Unknown


encodeFormula :: ExprBuilder t st fs
              -> Formula a
              -> Alphabet a
              -> IO (BoolExpr t)
encodeFormula sym _phi _alphabet = do
  p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
  q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
  orPred sym p q
