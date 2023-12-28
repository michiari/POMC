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
                                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import Pomc.Potl (Formula(..), getProps, normalize)
import Pomc.Check(makeOpa, InitialsComputation(..))
import Pomc.PropConv (APType, convProps, PropConv(encodeProp), encodeFormula )

import qualified Pomc.Encoding as E

import Pomc.Prob.SupportGraph(buildGraph, asPendingSemiconfs)

import qualified Pomc.CustoMap as CM

import Pomc.Prob.Z3Termination (terminationQuery, terminationQuerySCC)
import Pomc.Prob.ProbUtils
import Pomc.Prob.MiniProb (Program, programToPopa, Popa(..), ExprProp)

import qualified Pomc.Prob.GGraph as GG

import qualified Pomc.Prob.ProbEncoding as PE

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.IntSet as IntSet

import qualified Data.Map as Map

import Data.Bifunctor(first, second)

import Data.Hashable (Hashable)
import Control.Monad.ST (stToIO)

import Z3.Monad (evalZ3With, Logic(..))
import Z3.Opts

import qualified Debug.Trace as DBG
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Monad (when, unless)
import Data.Maybe (isNothing, isJust)

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
terminationLTExplicit popa bound = first toBool <$> terminationExplicit popa (CompQuery Lt bound PureSMT)

terminationLEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationLEExplicit popa bound = first toBool <$> terminationExplicit popa (CompQuery Le bound PureSMT)

terminationGTExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGTExplicit popa bound = first toBool <$> terminationExplicit popa (CompQuery Gt bound PureSMT)

terminationGEExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> Prob -> IO (Bool, String)
terminationGEExplicit popa bound = first toBool <$> terminationExplicit popa (CompQuery Ge bound PureSMT)

-- what is the probability that the input POPA terminates?
terminationApproxExplicit :: (Ord s, Hashable s, Show s, Ord a) => ExplicitPopa s a -> IO (Prob, String)
terminationApproxExplicit popa = first toProb <$> terminationExplicit popa (ApproxSingleQuery SMTWithHints)

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
    sc <- stToIO $ buildGraph pDelta (fst . epInitial $ popa) (E.encodeInput bitenc . Set.map (encodeProp pconv) . snd .  epInitial $ popa)
    scString <- stToIO $ CM.showMap sc
    --DBG.traceM $ "Computed the following support graph: " ++ scString
    asPendSemiconfs <- stToIO $ asPendingSemiconfs sc
    --DBG.traceM $ "(cannotReachPops, mustReachPops)" ++ show asPendSemiconfs
    p <- evalZ3With (Just QF_LRA) stdOpts (terminationQuery sc precFunc asPendSemiconfs query)

    DBG.traceM $ "Computed termination bounds: " ++ show p
    return (p, show query)

programTermination :: Program -> TermQuery -> IO (Prob, String)
programTermination prog query =
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
    sc <- stToIO $ buildGraph pDelta initVs initLbl
    -- asPendSemiconfs <- stToIO $ asPendingSemiconfs sc
    scString <- stToIO $ CM.showMap sc
    DBG.traceM $ "Length of the summary chain: " ++ show (MV.length sc)
    --p <- evalZ3With (Just QF_LRA) stdOpts $ terminationQuery sc precFunc asPendSemiconfs query
    (res, mustReachPopIdxs) <- evalZ3With (Just QF_LRA) stdOpts $ terminationQuerySCC sc precFunc query
    DBG.traceM $ "Computed termination probabilities: " ++ show res
    --let pendVectorLB = V.map (\k -> k < (1 :: Prob)) lb
    return (toProb res, scString ++ "\n" ++ show query)

-- QUALITATIVE MODEL CHECKING 
-- is the probability that the POPA satisfies phi equal to 1?
qualitativeModelCheck :: (Ord s, Hashable s, Show s)
                            => Formula APType -- input formula to check
                            -> Alphabet APType -- structural OP alphabet
                            -> (E.BitEncoding -> (s, Label)) -- POPA initial states
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- POPA Delta Push
                            -> (E.BitEncoding -> s -> RichDistr s Label) -- OPA Delta Shift
                            -> (E.BitEncoding -> s -> s -> RichDistr s Label) -- OPA Delta Pop
                            -> IO (Bool, String)
qualitativeModelCheck phi alphabet bInitials bDeltaPush bDeltaShift bDeltaPop =
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
    sc <- stToIO $ buildGraph wrapper (fst initial) (snd initial)
    scString <- stToIO $ CM.showMap sc
    {-
    asPendSemiconfs <- stToIO $ asPendingSemiconfs sc
    DBG.traceM $ "Computed the following asPending and asNotPending sets: " ++ show asPendSemiconfs
    pendVector <- toBoolVec <$> evalZ3With (Just QF_LRA) stdOpts (terminationQuery sc precFunc asPendSemiconfs $ PendingQuery SMTWithHints)
    almostSurely <- stToIO $ GG.qualitativeModelCheck wrapper (normalize phi) phiInitials sc pendVector
    -}
    (ApproxAllResult (vec, _), mustReachPopIdxs) <- evalZ3With (Just QF_LRA) stdOpts $ terminationQuerySCC sc precFunc $ ApproxAllQuery SMTWithHints
    DBG.traceM $ "Computed termination probabilities: " ++ show vec
    --let pendVectorLB = V.map (\k -> k < (1 :: Prob)) lb
    let cases i k
          | k < (1 :: Prob) && IntSet.member i mustReachPopIdxs = error $ "semiconf " ++ show i ++ "has a PAST certificate with termination probability below" ++ show k -- inconclusive result
          | k < (1 :: Prob) = True
          | IntSet.member i mustReachPopIdxs = False
          | otherwise = error $ "Semiconf " ++ show i ++ " has termination probability " ++ show k ++ " but it is not certified to be PAST."
        pendVector = V.imap cases vec
    DBG.traceM $ "Pending Vector: " ++ show pendVector
    DBG.traceM "Conclusive analysis!"
    almostSurely <- stToIO $ GG.qualitativeModelCheck wrapper (normalize phi) phiInitials sc pendVector
    return (almostSurely, scString ++ show pendVector)

qualitativeModelCheckProgram :: Formula ExprProp -- phi: input formula to check
                             -> Program -- input program
                             -> IO (Bool, String)
qualitativeModelCheckProgram phi prog =
  let
    (pconv, popa) = programToPopa prog (Set.fromList $ getProps phi)
    transPhi = encodeFormula pconv phi
  in qualitativeModelCheck transPhi (popaAlphabet popa) (popaInitial popa) (popaDeltaPush popa) (popaDeltaShift popa) (popaDeltaPop popa)

qualitativeModelCheckExplicit :: (Ord s, Hashable s, Show s)
                    => Formula APType -- phi: input formula to check
                    -> ExplicitPopa s APType -- input OPA
                    -> IO (Bool, String)
qualitativeModelCheckExplicit phi popa =
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
  in qualitativeModelCheck phi (epAlphabet popa) initial popaDeltaPush popaDeltaShift popaDeltaPop


qualitativeModelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a)
                              => Formula a -- phi: input formula to check
                              -> ExplicitPopa s a -- input OPA
                              -> IO (Bool, String)
qualitativeModelCheckExplicitGen phi popa =
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
  in qualitativeModelCheckExplicit tphi tPopa
