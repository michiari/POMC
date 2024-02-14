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
                                  , qualitativeModelCheckProgram
                                  , qualitativeModelCheckExplicit
                                  , qualitativeModelCheckExplicitGen
                                  , quantitativeModelCheckProgram
                                  , quantitativeModelCheckExplicit
                                  , quantitativeModelCheckExplicitGen
                                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import Pomc.Potl (Formula(..), getProps, normalize)
import Pomc.Check(makeOpa, InitialsComputation(..))
import Pomc.PropConv (APType, convProps, PropConv(encodeProp), encodeFormula)
import Pomc.TimeUtils (startTimer, stopTimer)

import qualified Pomc.Encoding as E

import Pomc.Prob.SupportGraph(buildGraph, asPendingSemiconfs)

import qualified Pomc.CustoMap as CM

import Pomc.Prob.Z3Termination (terminationQuerySCC)
import Pomc.Prob.ProbUtils
import Pomc.Prob.MiniProb (Program, programToPopa, Popa(..), ExprProp)

import qualified Pomc.Prob.GGraph as GG

import qualified Pomc.Prob.ProbEncoding as PE

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.IntSet as IntSet

import qualified Data.Map as Map

import Data.Bifunctor(second)

import Data.Hashable (Hashable)
import Control.Monad.ST (stToIO)

import Z3.Monad (evalZ3With, Logic(..))
import Z3.Opts

import qualified Debug.Trace as DBG
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Data.STRef (newSTRef, readSTRef)
import Numeric (showEFloat)

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
terminationLTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> Solver -> IO (Bool, Stats, String)
terminationLTExplicit popa bound solv = (\(res, s, str) -> (toBool res, s, str)) <$> terminationExplicit (CompQuery Lt bound solv) popa

terminationLEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> Solver -> IO (Bool, Stats, String)
terminationLEExplicit popa bound solv = (\(res, s, str) -> (toBool res, s, str)) <$> terminationExplicit (CompQuery Le bound solv) popa

terminationGTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> Solver -> IO (Bool, Stats, String)
terminationGTExplicit popa bound solv = (\(res, s, str) -> (toBool res, s, str)) <$> terminationExplicit (CompQuery Gt bound solv) popa

terminationGEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> Solver -> IO (Bool, Stats, String)
terminationGEExplicit popa bound solv = (\(res, s, str) -> (toBool res, s, str)) <$> terminationExplicit (CompQuery Ge bound solv) popa

-- what is the probability that the input POPA terminates?
terminationApproxExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Solver -> IO ((Prob, Prob), Stats, String)
terminationApproxExplicit popa solv = (\(ApproxSingleResult res, s, str) -> (res, s, str)) <$> terminationExplicit (ApproxSingleQuery solv) popa

-- handling the termination query
terminationExplicit :: (Ord s, Hashable s, Show s, Ord a)
                    => TermQuery
                    -> ExplicitPopa s a
                    -> IO (TermResult, Stats, String)
terminationExplicit query popa =
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
    stats <- stToIO $ newSTRef newStats
    sc <- stToIO $ buildGraph pDelta (fst . epInitial $ popa) (E.encodeInput bitenc . Set.map (encodeProp pconv) . snd .  epInitial $ popa) stats

    (res, _) <- evalZ3With (chooseLogic $ solver query) stdOpts $ terminationQuerySCC sc precFunc query stats
    DBG.traceM $ "Computed termination probability: " ++ show res
    computedStats <- stToIO $ readSTRef stats
    return (res, computedStats, show sc)

programTermination :: Solver -> Program -> IO (TermResult, Stats, String)
programTermination solver prog =
  let (_, popa) = programToPopa prog Set.empty
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
    stats <- stToIO $ newSTRef newStats
    sc <- stToIO $ buildGraph pDelta initVs initLbl stats
    (res, _) <- evalZ3With (chooseLogic solver) stdOpts $ terminationQuerySCC sc precFunc (ApproxSingleQuery solver) stats
    DBG.traceM $ "Computed termination probabilities: " ++ show res
    computedStats <- stToIO $ readSTRef stats
    return (res, computedStats, show sc)

-- QUALITATIVE MODEL CHECKING 
-- is the probability that the POPA satisfies phi equal to 1?
qualitativeModelCheck :: (Ord s, Hashable s, Show s)
                            => Solver
                            -> Formula APType -- input formula to check
                            -> Alphabet APType -- structural OP alphabet
                            -> (E.BitEncoding -> (s, Label)) -- POPA initial states
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- POPA Delta Push
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- OPA Delta Shift
                            -> (E.BitEncoding -> s -> s -> RichDistr s Label) -- OPA Delta Pop
                            -> IO (Bool, Stats, String)
qualitativeModelCheck solver phi alphabet bInitials bDeltaPush bDeltaShift bDeltaPop =
  let
    (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop, cl) =
      makeOpa phi IsProb alphabet (\_ _ -> True)

    deltaPush  = bDeltaPush bitenc
    deltaShift = bDeltaShift bitenc
    deltaPop  = bDeltaPop bitenc

    initial = bInitials bitenc

    proEnc = PE.makeProBitEncoding cl phiIsFinal

    phiPush p = (phiDeltaPush p Nothing)
    phiShift p = (phiDeltaShift p Nothing)

    wrapper = Delta
      { bitenc = bitenc
      , proBitenc = proEnc
      , prec = precFunc
      , deltaPush = deltaPush
      , deltaShift = deltaShift
      , deltaPop = deltaPop
      , phiDeltaPush = phiPush
      , phiDeltaShift = phiShift
      , phiDeltaPop = phiDeltaPop
      }
  in do
    stats <- stToIO $ newSTRef newStats
    sc <- stToIO $ buildGraph wrapper (fst initial) (snd initial) stats
    DBG.traceM $ "Length of the summary chain: " ++ show (V.length sc)
    (ApproxAllResult (_, ubMap), mustReachPopIdxs) <- evalZ3With (chooseLogic solver) stdOpts $ terminationQuerySCC sc precFunc (ApproxAllQuery solver) stats
    let ubTermMap = Map.mapKeysWith (+) fst ubMap
        ubVec =  V.generate (V.length sc) (\idx -> Map.findWithDefault 0 idx ubTermMap)
        cases i k
          | k < (1 - 100 * defaultRTolerance) && IntSet.member i mustReachPopIdxs = error $ "semiconf " ++ show i ++ "has a PAST certificate with termination probability equal to" ++ show k -- inconsistent result
          | k < (1 - 100 * defaultRTolerance) = True
          | IntSet.member i mustReachPopIdxs = False
          | otherwise = error $ "Semiconf " ++ show i ++ " has termination probability " ++ show k ++ " but it is not certified to be PAST." -- inconclusive result
        pendVector = V.imap cases ubVec
    DBG.traceM $ "Computed termination probabilities: " ++ show ubVec
    DBG.traceM $ "Pending Vector: " ++ show pendVector
    DBG.traceM "Conclusive analysis!"
    computedStats <- stToIO $ readSTRef stats
    DBG.traceM $ "Stats so far: " ++ concat [
        "Times: "
      , showEFloat (Just 4) (upperBoundTime computedStats) " s (upper bounds), "
      , showEFloat (Just 4) (pastTime computedStats) " s (PAST certificates), "
      , "\nInput pOPA state count: ", show $ popaStatesCount computedStats
      , "\nSupport graph size: ", show $ suppGraphLen computedStats
      , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquations computedStats
      , "\nSCC count in the support graph: ", show $ sccCount computedStats
      , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount computedStats
      , "\nLargest number of equations in an SCC in the Support Graph: ", show $ largestSCCEqsCount computedStats
      ]

    startGGTime <- startTimer
    almostSurely <- stToIO $ GG.qualitativeModelCheck wrapper (normalize phi) phiInitials sc pendVector

    tGG <- stopTimer startGGTime almostSurely

    return (almostSurely, computedStats { gGraphTime = tGG }, show sc ++ show pendVector)

qualitativeModelCheckProgram :: Solver
                             -> Formula ExprProp -- phi: input formula to check
                             -> Program -- input program
                             -> IO (Bool, Stats, String)
qualitativeModelCheckProgram solver phi prog =
  let
    (pconv, popa) = programToPopa prog (Set.fromList $ getProps phi)
    transPhi = encodeFormula pconv phi
  in qualitativeModelCheck solver transPhi (popaAlphabet popa) (popaInitial popa) (popaDeltaPush popa) (popaDeltaShift popa) (popaDeltaPop popa)

qualitativeModelCheckExplicit :: (Ord s, Hashable s, Show s)
                    => Solver
                    -> Formula APType -- phi: input formula to check
                    -> ExplicitPopa s APType -- input OPA
                    -> IO (Bool, Stats, String)
qualitativeModelCheckExplicit solver phi popa =
  let
    -- all the structural labels + all the labels which appear in phi
    essentialAP = Set.fromList $ End : (fst $ epAlphabet popa) ++ (getProps phi)

    maybeList Nothing = []
    maybeList (Just l) = l

    -- generate the delta relation of the input opa
    encodeDistr bitenc = map (\(s, b, p) -> (s, E.encodeInput bitenc (Set.intersection essentialAP b), p))
    makeDeltaMapI delta bitenc = Map.fromListWith (++) $
      map (\(q, distr) -> (q, encodeDistr bitenc distr))
          delta
    deltaPush  = makeDeltaMapI  (epopaDeltaPush popa)
    deltaShift  = makeDeltaMapI  (epopaDeltaShift popa)
    popaDeltaPush bitenc q = maybeList $ Map.lookup q (deltaPush bitenc)
    popaDeltaShift bitenc q = maybeList $ Map.lookup q (deltaShift bitenc)

    makeDeltaMapS delta bitenc = Map.fromListWith (++) $
      map (\(q, q', distr) -> ((q, q'), encodeDistr bitenc distr))
          delta
    deltaPop = makeDeltaMapS (epopaDeltaPop popa)
    popaDeltaPop bitenc q q' = maybeList $ Map.lookup (q, q') (deltaPop bitenc)

    initial bitenc = (fst . epInitial $ popa, E.encodeInput bitenc . Set.intersection essentialAP . snd .  epInitial $ popa)
  in qualitativeModelCheck solver phi (epAlphabet popa) initial popaDeltaPush popaDeltaShift popaDeltaPop


qualitativeModelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a)
                              => Solver
                              -> Formula a -- phi: input formula to check
                              -> ExplicitPopa s a -- input OPA
                              -> IO (Bool, Stats, String)
qualitativeModelCheckExplicitGen solver phi popa =
  let
    (sls, prec) = epAlphabet popa
    essentialAP = Set.fromList $ End : sls ++ getProps phi
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
  in qualitativeModelCheckExplicit solver tphi tPopa


-- QUANTITATIVE MODEL CHECKING
-- is the probability that the POPA satisfies phi equal to 1?
quantitativeModelCheck :: (Ord s, Hashable s, Show s)
                            => Solver
                            -> Formula APType -- input formula to check
                            -> Alphabet APType -- structural OP alphabet
                            -> (E.BitEncoding -> (s, Label)) -- POPA initial states
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- POPA Delta Push
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- OPA Delta Shift
                            -> (E.BitEncoding -> s -> s -> RichDistr s Label) -- OPA Delta Pop
                            -> IO ((Prob,Prob), Stats, String)
quantitativeModelCheck solver phi alphabet bInitials bDeltaPush bDeltaShift bDeltaPop =
  let
    (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop, cl) =
      makeOpa phi IsProb alphabet (\_ _ -> True)

    deltaPush  = bDeltaPush bitenc
    deltaShift = bDeltaShift bitenc
    deltaPop  = bDeltaPop bitenc

    initial = bInitials bitenc

    proEnc = PE.makeProBitEncoding cl phiIsFinal

    phiPush p = (phiDeltaPush p Nothing)
    phiShift p = (phiDeltaShift p Nothing)

    wrapper = Delta
      { bitenc = bitenc
      , proBitenc = proEnc
      , prec = precFunc
      , deltaPush = deltaPush
      , deltaShift = deltaShift
      , deltaPop = deltaPop
      , phiDeltaPush = phiPush
      , phiDeltaShift = phiShift
      , phiDeltaPop = phiDeltaPop
      }

  in do
    stats <- stToIO $ newSTRef newStats
    sc <- stToIO $ buildGraph wrapper (fst initial) (snd initial) stats
    DBG.traceM $ "Length of the summary chain: " ++ show (V.length sc)
    (ApproxAllResult (lbProbs, ubProbs), mustReachPopIdxs) <- evalZ3With (Just QF_LRA) stdOpts $ terminationQuerySCC sc precFunc (ApproxAllQuery solver) stats
    let ubTermMap = Map.mapKeysWith (+) fst ubProbs
        ubVec =  V.generate (V.length sc) (\idx -> Map.findWithDefault 0 idx ubTermMap)
        cases i k
          | k < (1 - 100 * defaultRTolerance) && IntSet.member i mustReachPopIdxs = error $ "semiconf " ++ show i ++ "has a PAST certificate with termination probability equal to" ++ show k -- inconsistent result
          | k < (1 - 100 * defaultRTolerance) = True
          | IntSet.member i mustReachPopIdxs = False
          | otherwise = error $ "Semiconf " ++ show i ++ " has termination probability " ++ show k ++ " but it is not certified to be PAST." -- inconclusive result
        pendVector = V.imap cases ubVec
    DBG.traceM $ "Computed upper bounds on termination probabilities: " ++ show ubVec
    DBG.traceM $ "Pending Upper Bounds Vector: " ++ show pendVector
    DBG.traceM "Conclusive analysis!"

    startGGTime <- startTimer
    (ub, lb) <- stToIO $ GG.quantitativeModelCheck wrapper (normalize phi) phiInitials sc mustReachPopIdxs lbProbs ubProbs stats

    tGG <- stopTimer startGGTime ub
    computedStats <- stToIO $ readSTRef stats

    return ((ub, lb), computedStats { gGraphTime = tGG }, show sc ++ show pendVector)

quantitativeModelCheckProgram :: Solver
                             -> Formula ExprProp -- phi: input formula to check
                             -> Program -- input program
                             -> IO ((Prob, Prob), Stats, String)
quantitativeModelCheckProgram solver phi prog =
  let
    (pconv, popa) = programToPopa prog (Set.fromList $ getProps phi)
    transPhi = encodeFormula pconv phi
  in quantitativeModelCheck solver transPhi (popaAlphabet popa) (popaInitial popa) (popaDeltaPush popa) (popaDeltaShift popa) (popaDeltaPop popa)

quantitativeModelCheckExplicit :: (Ord s, Hashable s, Show s)
                    => Solver
                    -> Formula APType -- phi: input formula to check
                    -> ExplicitPopa s APType -- input OPA
                    -> IO ((Prob,Prob), Stats, String)
quantitativeModelCheckExplicit solver phi popa =
  let
    -- all the structural labels + all the labels which appear in phi
    essentialAP = Set.fromList $ End : (fst $ epAlphabet popa) ++ (getProps phi)

    maybeList Nothing = []
    maybeList (Just l) = l

    -- generate the delta relation of the input opa
    encodeDistr bitenc = map (\(s, b, p) -> (s, E.encodeInput bitenc (Set.intersection essentialAP b), p))
    makeDeltaMapI delta bitenc = Map.fromListWith (++) $
      map (\(q, distr) -> (q, encodeDistr bitenc distr))
          delta
    deltaPush  = makeDeltaMapI  (epopaDeltaPush popa)
    deltaShift  = makeDeltaMapI  (epopaDeltaShift popa)
    popaDeltaPush bitenc q = maybeList $ Map.lookup q (deltaPush bitenc)
    popaDeltaShift bitenc q = maybeList $ Map.lookup q (deltaShift bitenc)

    makeDeltaMapS delta bitenc = Map.fromListWith (++) $
      map (\(q, q', distr) -> ((q, q'), encodeDistr bitenc distr))
          delta
    deltaPop = makeDeltaMapS (epopaDeltaPop popa)
    popaDeltaPop bitenc q q' = maybeList $ Map.lookup (q, q') (deltaPop bitenc)

    initial bitenc = (fst . epInitial $ popa, E.encodeInput bitenc . Set.intersection essentialAP . snd .  epInitial $ popa)
  in quantitativeModelCheck solver phi (epAlphabet popa) initial popaDeltaPush popaDeltaShift popaDeltaPop


quantitativeModelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a)
                              => Solver
                              -> Formula a -- phi: input formula to check
                              -> ExplicitPopa s a -- input OPA
                              -> IO ((Prob, Prob), Stats, String)
quantitativeModelCheckExplicitGen solver phi popa =
  let
    (sls, prec) = epAlphabet popa
    essentialAP = Set.fromList $ End : sls ++ getProps phi
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
  in quantitativeModelCheckExplicit solver tphi tPopa

chooseLogic :: Solver -> Maybe Logic
chooseLogic OVI = Just QF_LRA
chooseLogic _ = Just QF_NRA
