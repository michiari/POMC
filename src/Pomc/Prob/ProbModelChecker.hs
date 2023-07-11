{-# LANGUAGE DeriveGeneric, CPP #-}

{- |
   Module      : Pomc.Prob.ProbModelChecker
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbModelChecker ( Popa(..)
                                  , ExplicitPopa(..)
                                  ) where

#define NDEBUG

import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import qualified Pomc.Encoding as E
import Data.Set (Set)

type Prob = Double
newtype Distr a = Distr [(a, Prob)] deriving Show

data Popa s a = Popa
  { alphabet       :: Alphabet a -- OP alphabet
  , initial        :: s -- initial state of the POPA
  , popaDeltaPush  :: E.BitEncoding -> s -> Distr s -- push transition prob. distribution
  , popaDeltaShift :: E.BitEncoding -> s -> Distr s -- shift transition prob. distribution
  , popaDeltaPop   :: s -> s -> Distr s -- pop transition prob. distribution
  , labelling      :: s -> Set (Prop a) -- labelling function
  }

data ExplicitPopa s a = ExplicitPopa
  { epAlphabet       :: Alphabet a -- OP alphabet
  , epInitial        :: s -- initial state of the POPA
  , epopaDeltaPush   :: [(s, Distr s)] -- push transition prob. distribution
  , epopaDeltaShift  :: [(s, Distr s)]-- shift transition prob. distribution
  , epopaDeltaPop    :: [(s, s, Distr s)]-- pop transition prob. distribution
  , elabelling       :: [(s, Set (Prop a))] -- labelling function
  } deriving (Show)
