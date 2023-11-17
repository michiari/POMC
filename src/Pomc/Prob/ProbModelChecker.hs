{-# LANGUAGE DeriveGeneric, CPP #-}

{- |
   Module      : Pomc.Prob.ProbModelChecker
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbModelChecker ( ExplicitPopa(..)
                                  , terminationLTExplicit
                                  , terminationLEExplicit
                                  , terminationGTExplicit
                                  , terminationGEExplicit
                                  , terminationApproxExplicit
                                  , programTermination
                                  ) where
import Prelude hiding (LT,GT)
import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import Pomc.Potl (Formula(T))
import Pomc.Check(makeOpa)
import Pomc.PropConv ( convProps, PropConv(encodeProp) )

import qualified Pomc.Encoding as E

import Pomc.Prob.SupportChain (decomposeGraph)

import qualified Pomc.CustoMap as CM

import Pomc.Prob.Z3Termination (terminationQuery)
import Pomc.Prob.ProbUtils
import Pomc.Prob.MiniProb (Program, programToPopa, Popa(..))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.Bifunctor(first)


import Data.Hashable ( Hashable )
import Control.Monad.ST (stToIO)

import Z3.Monad (evalZ3)

-- TODO: add normalize RichDistr to optimize the encoding
data ExplicitPopa s a = ExplicitPopa
  { epAlphabet       :: Alphabet a -- OP alphabet
  , epInitial        :: (s, Set (Prop a)) -- initial state of the POPA
  , epopaDeltaPush   :: [(s, RichDistr s (Set (Prop a)))] -- push transition prob. distribution
  , epopaDeltaShift  :: [(s, RichDistr s (Set (Prop a)))] -- shift transition prob. distribution
  , epopaDeltaPop    :: [(s, s, RichDistr s (Set (Prop a)))] -- pop transition prob. distribution
  } deriving (Show)

terminationLTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationLTExplicit popa bound = (first toBool) <$> terminationExplicit popa (LT bound)

terminationLEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationLEExplicit popa bound = (first toBool) <$> terminationExplicit popa (LE bound)

terminationGTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGTExplicit popa bound = (first toBool) <$> terminationExplicit popa (GT bound)

terminationGEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGEExplicit popa bound = (first toBool) <$> terminationExplicit popa (GE bound)

terminationApproxExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> IO (Prob, String)
terminationApproxExplicit popa = (first toProb) <$> terminationExplicit popa ApproxSingleQuery

terminationExplicit :: (Ord s, Hashable s, Show s, Ord a)
                    => ExplicitPopa s a
                    -> TermQuery
                    -> IO (TermResult, String)
terminationExplicit popa query =
  let
    (sls, prec) = epAlphabet popa
    (_, tprec, [tsls], pconv) = convProps T prec [sls]

    (bitenc, precFunc, _, _, _, _, _, _) =
      makeOpa T False (tsls, tprec) (\_ _ -> True)

    maybeList Nothing = []
    maybeList (Just l) = l

    -- generate the delta relation of the input opa
    encodeDistr = map (\(s, b, p) -> (s, E.encodeInput bitenc (Set.map (encodeProp pconv) b), p))
    makeDeltaMapI delta = Map.fromListWith (++) $
      map (\(q, distr) -> (q, encodeDistr  distr))
          delta
    deltaPush  = makeDeltaMapI  (epopaDeltaPush popa)
    deltaShift  = makeDeltaMapI  (epopaDeltaShift popa)
    popaDeltaPush  q = maybeList $ Map.lookup q deltaPush
    popaDeltaShift  q = maybeList $ Map.lookup q deltaShift

    makeDeltaMapS  delta = Map.fromListWith (++) $
      map (\(q, q', distr) -> ((q, q'), encodeDistr  distr))
          delta
    deltaPop = makeDeltaMapS   (epopaDeltaPop popa)
    popaDeltaPop  q q' = maybeList $ Map.lookup (q, q') deltaPop

    pDelta = Delta
            { bitenc = bitenc
            , prec = precFunc
            , deltaPush = popaDeltaPush
            , deltaShift = popaDeltaShift
            , deltaPop = popaDeltaPop
            }

  in do
    sc <- stToIO $ decomposeGraph pDelta (fst . epInitial $ popa) (E.encodeInput bitenc . Set.map (encodeProp pconv) . snd .  epInitial $ popa)
    scString <- stToIO $ CM.showMap sc
    p <- evalZ3 $ terminationQuery sc precFunc query
    return (p, scString ++ "\nDeltaPush: " ++ show deltaPush ++ "\nDeltaShift: " ++ show deltaShift ++ "\nDeltaPop: " ++ show deltaPop ++ "\n" ++ show query)

programTermination :: Program -> TermQuery -> IO (TermResult, String)
programTermination prog query =
  let (_, popa) = programToPopa False prog Set.empty
      (tsls, tprec) = popaAlphabet popa
      (bitenc, precFunc, _, _, _, _, _, _) =
        makeOpa T False (tsls, tprec) (\_ _ -> True)

      (initVs, initLbl) = popaInitial popa bitenc
      pDelta = Delta
               { bitenc = bitenc
               , prec = precFunc
               , deltaPush = popaDeltaPush popa bitenc
               , deltaShift = popaDeltaShift popa bitenc
               , deltaPop = popaDeltaPop popa bitenc
               }

  in do
    sc <- stToIO $ decomposeGraph pDelta initVs initLbl
    scString <- stToIO $ CM.showMap sc
    p <- evalZ3 $ terminationQuery sc precFunc query
    return (p, scString ++ "\n" ++ show query)
