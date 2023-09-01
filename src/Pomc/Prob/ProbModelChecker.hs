{-# LANGUAGE DeriveGeneric, CPP #-}

{- |
   Module      : Pomc.Prob.ProbModelChecker
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbModelChecker ( Popa(..)
                                  , ExplicitPopa(..)
                                  , terminationExplicit
                                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import qualified Pomc.Encoding as E
import Data.Set (Set)
import qualified Data.Set as Set 

import qualified Data.Map as Map

import Pomc.Check(makeOpa)
import Pomc.PropConv ( convProps, PropConv(encodeProp) )

import Pomc.Prob.SummaryChain(decomposeGraph, ProbDelta)
import qualified Pomc.Prob.SummaryChain as SC
import Pomc.Prob.Z3Termination(terminationQuery)
import Pomc.Prob.ProbUtils(Prob, RichDistr, Label)
import Data.Hashable
import Pomc.Potl (Formula(T))
import Control.Monad.ST (stToIO)

data Popa s a = Popa
  { alphabet       :: Alphabet a -- OP alphabet
  , initial        :: (s, Label) -- initial state of the POPA
  , popaDeltaPush  :: E.BitEncoding -> s -> RichDistr s Label -- push transition prob. distribution
  , popaDeltaShift :: E.BitEncoding -> s -> RichDistr s Label -- shift transition prob. distribution
  , popaDeltaPop   :: s -> s -> RichDistr s Label -- pop transition prob. distribution
  , labelling      :: s -> Set (Prop a) -- labelling function
  }

-- TODO: add normalize RichDistr to optimize the encoding
data ExplicitPopa s a = ExplicitPopa
  { epAlphabet       :: Alphabet a -- OP alphabet
  , epInitial        :: (s, Set (Prop a)) -- initial state of the POPA
  , epopaDeltaPush   :: [(s, RichDistr s (Set (Prop a)))] -- push transition prob. distribution
  , epopaDeltaShift  :: [(s, RichDistr s (Set (Prop a)))] -- shift transition prob. distribution
  , epopaDeltaPop    :: [(s, s, RichDistr s (Set (Prop a)))] -- pop transition prob. distribution
  } deriving (Show)


terminationExplicit :: (Ord s, Hashable s, Show s, Ord a)
                    => ExplicitPopa s a
                    -> Prob
                    -> IO (Maybe Rational)
terminationExplicit popa prob = 
  let 
    (sls, prec) = epAlphabet popa
    (_, tprec, [tsls], pconv) = convProps T prec [sls]
    
    (bitenc, precFunc, _, _, _, _, _, _) =
      makeOpa T False (tsls, tprec) (\_ _ -> True)

    maybeList Nothing = []
    maybeList (Just l) = l
    
    -- generate the delta relation of the input opa
    encodeDistr = map (\(s, b, p) -> (s, E.encodeInput bitenc (Set.map (encodeProp pconv) b), p))
    makeDeltaMapI delta = Map.fromList $
      map (\(q, distr) -> (q, encodeDistr  distr))
          delta
    deltaPush  = makeDeltaMapI  (epopaDeltaPush popa)
    deltaShift  = makeDeltaMapI  (epopaDeltaShift popa)
    popaDeltaPush  q = maybeList $ Map.lookup q (deltaPush ) 
    popaDeltaShift  q = maybeList $ Map.lookup q (deltaShift  )

    makeDeltaMapS  delta = Map.fromList $
      map (\(q, q', distr) -> ((q, q'), encodeDistr  distr))
          delta
    popaDeltaPop  q q' = maybeList $ Map.lookup (q, q') $ makeDeltaMapS   (epopaDeltaPop popa) 

    pDelta = SC.Delta
            { SC.bitenc = bitenc
            , SC.prec = precFunc
            , SC.deltaPush = popaDeltaPush
            , SC.deltaShift = popaDeltaShift
            , SC.deltaPop = popaDeltaPop
            }
  in do 
    sc <- stToIO $ decomposeGraph pDelta (fst . epInitial $ popa) (E.encodeInput bitenc . Set.map (encodeProp pconv) . snd .  epInitial $ popa)
    terminationQuery sc precFunc prob
