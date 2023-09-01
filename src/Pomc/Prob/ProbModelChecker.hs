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

import Pomc.Prob.Termination(terminationProbs)
import Pomc.Prob.ProbUtils(Prob, RichDistr, Label)

data Popa s a = Popa
  { alphabet       :: Alphabet a -- OP alphabet
  , initial        :: (s, Label) -- initial state of the POPA
  , popaDeltaPush  :: E.BitEncoding -> s -> RichDistr s Label -- push transition prob. distribution
  , popaDeltaShift :: E.BitEncoding -> s -> RichDistr s Label -- shift transition prob. distribution
  , popaDeltaPop   :: s -> s -> RichDistr s Label -- pop transition prob. distribution
  , labelling      :: s -> Set (Prop a) -- labelling function
  }

data ExplicitPopa s a = ExplicitPopa
  { epAlphabet       :: Alphabet a -- OP alphabet
  , epInitial        :: (s, Set (Prop a)) -- initial state of the POPA
  , epopaDeltaPush   :: [(s, RichDistr s (Set (Prop a)))] -- push transition prob. distribution
  , epopaDeltaShift  :: [(s, RichDistr s (Set (Prop a)))] -- shift transition prob. distribution
  , epopaDeltaPop    :: [(s, s, RichDistr s (Set (Prop a)))] -- pop transition prob. distribution
  } deriving (Show)
