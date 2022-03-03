{-# LANGUAGE DeriveGeneric, CPP #-}

{- |
   Module      : Pomc.ModelChecker
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.ModelChecker ( ExplicitOpa(..)
                         , modelCheck
                         , modelCheckExplicit
                         , modelCheckExplicitGen
                         , modelCheckProgram
                         , countStates
                         ) where

#define NDEBUG

import Pomc.Prop (Prop(..))
import Pomc.Prec (Alphabet)
import Pomc.Potl (Formula(..), getProps)
import Pomc.Check (makeOpa)
import Pomc.State(Input, State(..))
import Pomc.SatUtil(SatState(..))
import Pomc.Satisfiability (isEmpty, isEmptyOmega)
import qualified Pomc.Satisfiability as Sat (Delta(..))
import Pomc.PropConv (APType, PropConv(..), convProps, encodeFormula)
import qualified Pomc.Encoding as E (PropSet, BitEncoding, encodeInput)
import Pomc.MiniProc (Program, VarState, programToOpa)
#ifndef NDEBUG
import Pomc.Satisfiability (toInputTrace, showTrace)
import qualified Debug.Trace as DBG
#else
import Pomc.Satisfiability (toInputTrace)
#endif

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.HashMap.Strict as Map
import Data.Text (Text)

import GHC.Generics (Generic)
import Data.Hashable

import Control.DeepSeq(NFData(..), deepseq)

data ExplicitOpa s a = ExplicitOpa
  { eoAlphabet :: Alphabet a -- OP alphabet
  , eoInitials   :: [s] -- initial states of the OPA
  , eoFinals     :: [s] -- final states of the OPA
  , eoDeltaPush  :: [(s, Set (Prop a), [s])] -- push transition relation
  , eoDeltaShift :: [(s, Set (Prop a), [s])] -- shift transition relation
  , eoDeltaPop   :: [(s, s, [s])] -- pop transition relation
  } deriving (Show)

-- a specific type for the model checker state: the parametric s is for the input OPA, the second field is for the generated opa from the input formula
data MCState s = MCState s State deriving (Generic, Eq, Show, Ord)

instance NFData (MCState s) where
  rnf (MCState _ s2) = s2 `deepseq` ()

instance Hashable s => Hashable (MCState s)

instance SatState (MCState s) where
  getSatState (MCState _ p) = p
  {-# INLINABLE getSatState #-}

  getStateProps bitenc (MCState _ p) = getStateProps bitenc p
  {-# INLINABLE getStateProps #-}

-- generate the cartesian product between two lists of states (the first list has a generic type)
cartesian :: [a] -> [State] -> [MCState a]
cartesian xs ys = [MCState x y | x <- xs, y <- ys]

#ifndef NDEBUG
modelCheck :: (Ord s, Hashable s, Show s, Show a)
#else
modelCheck :: (Ord s, Hashable s, Show s)
#endif
           => Bool -- is it the infinite case?
           -> Formula APType -- input formula to check
           -> Alphabet APType -- structural OP alphabet
           -> [s] -- OPA initial states
           -> (s -> Bool) -- OPA isFinal
           -> (E.BitEncoding -> s -> Input -> [s]) -- OPA Delta Push
           -> (E.BitEncoding -> s -> Input -> [s]) -- OPA Delta Shift
           -> (s -> s -> [s]) -- OPA Delta Pop
#ifndef NDEBUG
           -> PropConv a
#endif
           -> (Bool, [(s, E.PropSet)]) -- (does the OPA satisfy the formula?, counterexample trace)
modelCheck isOmega phi alphabet opaInitials opaIsFinal opaDeltaPush opaDeltaShift opaDeltaPop
#ifndef NDEBUG
  pconv
#endif
  =
  let -- generate the OPA associated to the negation of the input formula
    (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop, cl) =
      makeOpa (Not phi) isOmega alphabet

    -- compute the cartesian product between the initials of the two opas
    cInitials = cartesian opaInitials phiInitials
    -- new isFinal function for the cartesian product:
    -- both underlying opas must be in an acceptance state
    cIsFinal (MCState q p) = opaIsFinal q && phiIsFinal T p
    cIsFinalOmega states =
      (any (\(MCState q _) -> opaIsFinal q) states) &&
      (all (\f -> (any (\(MCState _ p) -> phiIsFinal f p) states)) $ Set.toList cl)

    cDeltaPush (MCState q p) b = cartesian (opaDeltaPush bitenc q b) (phiDeltaPush p Nothing)
    cDeltaShift (MCState q p) b = cartesian (opaDeltaShift bitenc q b) (phiDeltaShift p Nothing)
    cDeltaPop (MCState q p) (MCState q' p') = cartesian (opaDeltaPop q q') (phiDeltaPop p p')

    cDelta = Sat.Delta
             { Sat.bitenc = bitenc
             , Sat.prec = precFunc
             , Sat.deltaPush = cDeltaPush
             , Sat.deltaShift = cDeltaShift
             , Sat.deltaPop = cDeltaPop
             }
    (sat, trace) = if isOmega
                   then isEmptyOmega cDelta cInitials cIsFinalOmega
                   else isEmpty cDelta cInitials cIsFinal
#ifndef NDEBUG
  in DBG.trace (showTrace bitenc pconv trace)
#else
  in
#endif
     (sat, map (\(MCState q _, b) -> (q, b)) $ toInputTrace bitenc trace)


#ifndef NDEBUG
modelCheckExplicit :: (Ord s, Hashable s, Show s, Show a)
#else
modelCheckExplicit :: (Ord s, Hashable s, Show s)
#endif
           => Bool -- is it the infinite case?
           -> Formula APType -- input formula to check
           -> ExplicitOpa s APType -- input OPA
#ifndef NDEBUG
           -> PropConv a
#endif
           -> (Bool, [(s, E.PropSet)]) -- (does the OPA satisfy the formula?, counterexample trace)
#ifndef NDEBUG
modelCheckExplicit isOmega phi opa pconv =
#else
modelCheckExplicit isOmega phi opa =
#endif
  let -- fromList removes duplicates
      -- all the structural labels + all the labels which appear in phi
      essentialAP = Set.fromList $ End : (fst $ eoAlphabet opa) ++ (getProps phi)

      opaIsFinal q = Set.member q (Set.fromList $ eoFinals opa)

      -- unwrap an object of type Maybe List
      maybeList Nothing = []
      maybeList (Just l) = l

      -- generate the delta relation of the input opa
      makeDeltaMapI bitenc delta = Map.fromListWith (++) $
        map (\(q', b', ps) -> ((q', E.encodeInput bitenc $ Set.intersection essentialAP b'), ps))
            delta
      makeDeltaMapS delta = Map.fromList $ map (\(q', b', ps) -> ((q', b'), ps)) delta
      opaDeltaPush bitenc q b =
        maybeList $ Map.lookup (q, b) $ makeDeltaMapI bitenc (eoDeltaPush opa)
      opaDeltaShift bitenc q b =
        maybeList $ Map.lookup (q, b) $ makeDeltaMapI bitenc (eoDeltaShift opa)
      opaDeltaPop q q' = maybeList $ Map.lookup (q, q') $ makeDeltaMapS (eoDeltaPop opa)

  in modelCheck isOmega phi (eoAlphabet opa) (eoInitials opa)
     opaIsFinal opaDeltaPush opaDeltaShift opaDeltaPop
#ifndef NDEBUG
     pconv
#endif


#ifndef NDEBUG
modelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a, Show a)
#else
modelCheckExplicitGen :: (Ord s, Hashable s, Show s, Ord a)
#endif
              => Bool
              -> Formula a
              -> ExplicitOpa s a
              -> (Bool, [(s, Set (Prop a))])
modelCheckExplicitGen isOmega phi opa =
  let (sls, prec) = eoAlphabet opa
      (tphi, tprec, [tsls], pconv) = convProps phi prec [sls]
      transDelta delta = map (\(q, b, p) -> (q, Set.map (encodeProp pconv) b, p)) delta
      tOpa = opa { eoAlphabet   = (tsls, tprec)
                 , eoDeltaPush  = transDelta (eoDeltaPush opa)
                 , eoDeltaShift = transDelta (eoDeltaShift opa)
                 }
#ifndef NDEBUG
      (sat, trace) = modelCheckExplicit isOmega tphi tOpa pconv
#else
      (sat, trace) = modelCheckExplicit isOmega tphi tOpa
#endif
  in (sat, map (\(q, b) -> (q, Set.map (decodeProp pconv) b)) trace)

-- count all the states of an input ExplicitOpa
countStates :: Ord s => ExplicitOpa s a -> Int
countStates opa =
  let foldDeltaInput set (q, _, ps) = set `Set.union` (Set.fromList (q : ps))
      pushStates = foldl foldDeltaInput Set.empty (eoDeltaPush opa)
      shiftStates = foldl foldDeltaInput pushStates (eoDeltaShift opa)
      popStates = foldl (\set (q, r, ps) -> set `Set.union` (Set.fromList (q : r : ps)))
                  shiftStates (eoDeltaPop opa)
  in Set.size $ popStates `Set.union` (Set.fromList $ eoInitials opa ++ eoFinals opa)

modelCheckProgram :: Bool
                  -> Formula Text
                  -> Program
                  -> (Bool, [(VarState, Set (Prop Text))])
modelCheckProgram isOmega phi prog =
  let (pconv, alphabet, ini, isfin, dpush, dshift, dpop) =
        programToOpa isOmega prog (Set.fromList $ getProps phi)
      transPhi = encodeFormula pconv phi
      (sat, trace) = modelCheck isOmega transPhi alphabet ini isfin dpush dshift dpop
#ifndef NDEBUG
                     pconv
#endif
  in (sat, map (\(q, b) -> (q, Set.map (decodeProp pconv) b)) trace)
