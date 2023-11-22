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
                                  , qualitativeModelCheckExplicit
                                  , qualitativeModelCheckExplicitGen
                                  ) where
import Prelude hiding (LT,GT)
import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import Pomc.Potl (Formula(..), getProps)
import Pomc.Check(makeOpa, InitialsComputation(..))
import Pomc.PropConv (APType, convProps, PropConv(encodeProp) )

import qualified Pomc.Encoding as E

import Pomc.Prob.SupportGraph(decomposeGraph)

import qualified Pomc.CustoMap as CM

import Pomc.Prob.Z3Termination (terminationQuery)
import Pomc.Prob.ProbUtils
import Pomc.Prob.MiniProb (Program, programToPopa, Popa(..))

import qualified Pomc.Prob.GGraph as GG

import qualified Pomc.Prob.ProbEncoding as PE

import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Map as Map

import Data.Bifunctor(first, second)

import Data.Hashable (Hashable)
import Control.Monad.ST (stToIO)

import Z3.Monad (evalZ3With, Logic(..))
import Z3.Opts

-- TODO: add normalize RichDistr to optimize the encoding
-- note that non normalized encodings are at the moment (16.11.23) correctly handled by the termination algorithms
data ExplicitPopa s a = ExplicitPopa
  { epAlphabet       :: Alphabet a -- OP alphabet
  , epInitial        :: (s, Set (Prop a)) -- initial state of the POPA
  , epopaDeltaPush   :: [(s, RichDistr s (Set (Prop a)))] -- push transition prob. distribution
  , epopaDeltaShift  :: [(s, RichDistr s (Set (Prop a)))] -- shift transition prob. distribution
  , epopaDeltaPop    :: [(s, s, RichDistr s (Set (Prop a)))] -- pop transition prob. distribution
  } deriving (Show)

------------------------------------------------
-- set of APIs for explicitly presented POPAs --
------------------------------------------------ 

-- TERMINATION
-- is the probability to terminate respectively <, <=, >=, > than the given probability?
-- (the return String is a debugging message for developing purposes)
terminationLTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationLTExplicit popa bound = first toBool <$> terminationExplicit popa (LT bound)

terminationLEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationLEExplicit popa bound = first toBool <$> terminationExplicit popa (LE bound)

terminationGTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGTExplicit popa bound = first toBool <$> terminationExplicit popa (GT bound)

terminationGEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGEExplicit popa bound = first toBool <$> terminationExplicit popa (GE bound)

-- what is the probability that the input POPA terminates?
terminationApproxExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> IO (Prob, String)
terminationApproxExplicit popa = first toProb <$> terminationExplicit popa ApproxSingleQuery

-- handling the termination query
terminationExplicit :: (Ord s, Hashable s, Show s, Ord a)
                    => ExplicitPopa s a
                    -> TermQuery
                    -> IO (TermResult, String)
terminationExplicit popa query =
  let
    (sls, prec) = epAlphabet popa
    (_, tprec, [tsls], pconv) = convProps T prec [sls]

    -- I don't actually care, I just need the bitenc
    (bitenc, precFunc, _, _, _, _, _, _) =
      makeOpa T IsProb (tsls, tprec) (\_ _ -> True)

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
    debug scString $ return ()
    p <- evalZ3With (Just QF_NRA) stdOpts $ terminationQuery sc precFunc query
    return (p, scString ++ "\nDeltaPush: " ++ show deltaPush ++ "\nDeltaShift: " ++ show deltaShift ++ "\nDeltaPop: " ++ show deltaPop ++ "\n" ++ show query)

programTermination :: Program -> TermQuery -> IO (TermResult, String)
programTermination prog query =
  let (_, popa) = programToPopa False prog Set.empty
      (tsls, tprec) = popaAlphabet popa
      (bitenc, precFunc, _, _, _, _, _, _) =
        makeOpa T IsProb (tsls, tprec) (\_ _ -> True)

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
    debug scString $ return ()
    p <- evalZ3With (Just QF_NRA) stdOpts $ terminationQuery sc precFunc query
    return (p, scString ++ "\n" ++ show query)

-- QUALITATIVE MODEL CHECKING 
-- is the probability that the POPA satisfies phi equal to 1?
qualitativeModelCheckExplicit :: (Ord s, Hashable s, Show s)
                    => Formula APType -- phi: input formula to check
                    -> ExplicitPopa s APType -- input OPA
                    -> IO (Bool, String)
qualitativeModelCheckExplicit phi popa =
  let
    -- all the structural labels + all the labels which appear in phi
    essentialAP = Set.fromList $ (fst $ epAlphabet popa) ++ (getProps phi)

    (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop, cl) =
      makeOpa phi IsProb (epAlphabet popa) (\_ _ -> True)

    maybeList Nothing = []
    maybeList (Just l) = l

    -- generate the delta relation of the input opa
    encodeDistr = map (\(s, b, p) -> (s, E.encodeInput bitenc (Set.intersection essentialAP b), p))
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

    proEnc = PE.makeProBitEncoding cl phiIsFinal

    phiPush p = (phiDeltaPush p Nothing)
    phiShift p = (phiDeltaShift p Nothing)

    wrapper = GG.Delta
              { GG.bitenc = bitenc
              , GG.proBitenc = proEnc
              , GG.prec = precFunc
              , GG.deltaPush = popaDeltaPush
              , GG.deltaShift = popaDeltaShift
              , GG.deltaPop = popaDeltaPop
              , GG.phiDeltaPush = phiPush
              , GG.phiDeltaShift = phiShift
              , GG.phiDeltaPop = phiDeltaPop
              }
  in do
    sc <- stToIO $ decomposeGraph pDelta (fst . epInitial $ popa) (E.encodeInput bitenc . Set.intersection essentialAP . snd .  epInitial $ popa)
    scString <- stToIO $ CM.showMap sc
    debug scString $ return ()
    pendVector <- evalZ3With (Just QF_NRA) stdOpts $ terminationQuery sc precFunc PendingQuery
    debug (show pendVector) $ return ()
    (g, i) <- stToIO $ GG.decomposeGGraph wrapper phiInitials (MV.unsafeRead sc) (toBoolVec pendVector V.!)
    gString <- stToIO $ CM.showMap g
    debug gString $ return (True, scString ++ show pendVector ++ gString)

qualitativeModelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a)
                              => Formula a -- phi: input formula to check
                              -> ExplicitPopa s a -- input OPA
                              -> IO (Bool, String)
qualitativeModelCheckExplicitGen phi popa =
  let
    (sls, prec) = epAlphabet popa
    essentialAP = Set.fromList $ sls ++ getProps phi
    (tphi, tprec, [tsls], pconv) = convProps phi prec [sls]
    transDelta = map (second
                        (map (\(a, b, p) -> 
                            (a, Set.map (encodeProp pconv) $ Set.intersection essentialAP b, p))
                        )
                     )
    transDeltaPop = map ( \(q,q0, distr) -> (q,q0,
                                                  map (\(a, b, p) -> 
                                                    (a, Set.map (encodeProp pconv) $ Set.intersection essentialAP b, p))
                                                  distr
                                            )
                        )
    transInitial = second (Set.map (encodeProp pconv) . Set.intersection essentialAP)
    tPopa = popa { epAlphabet   = (tsls, tprec)
                , epInitial = transInitial (epInitial popa)
                 , epopaDeltaPush  = transDelta (epopaDeltaPush popa)
                 , epopaDeltaShift = transDelta (epopaDeltaShift popa)
                 , epopaDeltaPop = transDeltaPop (epopaDeltaPop popa)
                 }
  in qualitativeModelCheckExplicit tphi tPopa