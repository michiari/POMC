{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.ModelChecker
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.ModelChecker (
                           ExplicitOpa(..)
                         , modelCheck
                         , modelCheckGen
                         , extractALs
                         , countStates
                         ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (StructPrecRel)
import Pomc.PotlV2 (Formula(..), getProps)
import Pomc.Check (State, makeOpa)
import Pomc.Satisfiability (SatState(..), isEmpty)
import qualified Pomc.Satisfiability as Sat (Delta(..))
import Pomc.PropConv (APType, convAP)
import qualified Pomc.Data as D (encodeInput)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Map as Map

import GHC.Generics (Generic)
import Data.Hashable

data ExplicitOpa s a = ExplicitOpa
  { sigma :: ([Prop a], [Prop a]) -- the alphabet (the first list is for structural labels, the second one is for normal labels)
  , precRel :: [StructPrecRel a] --precedence relation between structural labels of the alphabet
  , initials   :: [s] -- initial states of the OPA
  , finals     :: [s] -- final states of the OPA
  , deltaPush  :: [(s, Set (Prop a), [s])] --push transition relation
  , deltaShift :: [(s, Set (Prop a), [s])] -- shift transition relation
  , deltaPop   :: [(s, s, [s])] -- pop transition relation
  } deriving (Show)

data MCState s = MCState s State deriving (Generic, Eq, Show)

instance Hashable s => Hashable (MCState s)

instance SatState (MCState s) where
  getSatState (MCState _ p) = p
  {-# INLINABLE getSatState #-}

  getStateProps bitenc (MCState _ p) = getStateProps bitenc p
  {-# INLINABLE getStateProps #-}


cartesian :: [a] -> [State] -> [MCState a]
cartesian xs ys = [MCState x y | x <- xs, y <- ys]

modelCheck :: (Ord s, Hashable s, Show s)
           => Formula APType
           -> ExplicitOpa s APType
           -> Bool
modelCheck phi opa =
  let essentialAP = Set.fromList $ End : (fst $ sigma opa) ++ (getProps phi)

      (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop) =
        makeOpa (Not phi) (fst $ sigma opa, getProps phi) (precRel opa)

      cInitials = cartesian (initials opa) phiInitials
      cIsFinal (MCState q p) = Set.member q (Set.fromList $ finals opa) && phiIsFinal p

      maybeList Nothing = []
      maybeList (Just l) = l

      makeDeltaMapI delta = Map.fromListWith (++) $
        map (\(q', b', ps) -> ((q', D.encodeInput bitenc $ Set.intersection essentialAP b'), ps))
            delta
      makeDeltaMapS delta = Map.fromList $ map (\(q', b', ps) -> ((q', b'), ps)) delta
      opaDeltaPush q b = maybeList $ Map.lookup (q, b) $ makeDeltaMapI (deltaPush opa)
      opaDeltaShift q b = maybeList $ Map.lookup (q, b) $ makeDeltaMapI (deltaShift opa)
      opaDeltaPop q q' = maybeList $ Map.lookup (q, q') $ makeDeltaMapS (deltaPop opa)

      cDeltaPush (MCState q p) b = cartesian (opaDeltaPush q b) (phiDeltaPush p b)
      cDeltaShift (MCState q p) b = cartesian (opaDeltaShift q b) (phiDeltaShift p b)
      cDeltaPop (MCState q p) (MCState q' p') = cartesian (opaDeltaPop q q') (phiDeltaPop p p')

      cDelta = Sat.Delta
               { Sat.bitenc = bitenc
               , Sat.prec = precFunc
               , Sat.deltaPush = cDeltaPush
               , Sat.deltaShift = cDeltaShift
               , Sat.deltaPop = cDeltaPop
               }

  in isEmpty cDelta cInitials cIsFinal

modelCheckGen :: ( Ord s, Hashable s, Show s, Ord a)
              => Formula a
              -> ExplicitOpa s a
              -> Bool
modelCheckGen phi opa =
  let (sls, als) = sigma opa
      (tphi, tprec, trans) = convAP phi (precRel opa) (sls ++ (getProps phi) ++ als)
      transProps props = fmap (fmap trans) props
      transDelta delta = map (\(q, b, p) -> (q, Set.map (fmap trans) b, p)) delta
      tOpa = ExplicitOpa
             { sigma      = (transProps sls, transProps als)
             , precRel    = tprec
             , initials   = (initials opa)
             , finals     = (finals opa)
             , deltaPush  = transDelta (deltaPush opa)
             , deltaShift = transDelta (deltaShift opa)
             , deltaPop   = deltaPop opa
             }
  in modelCheck tphi tOpa

extractALs :: Ord a => [(s, Set (Prop a), [s])] -> [Prop a]
extractALs deltaRels = Set.toList $ foldl (\als (_, a, _) -> als `Set.union` a) Set.empty deltaRels

countStates :: Ord s => ExplicitOpa s a -> Int
countStates opa =
  let foldDeltaInput set (q, _, ps) = set `Set.union` (Set.fromList (q : ps))
      pushStates = foldl foldDeltaInput Set.empty (deltaPush opa)
      shiftStates = foldl foldDeltaInput pushStates (deltaShift opa)
      popStates = foldl (\set (q, r, ps) -> set `Set.union` (Set.fromList (q : r : ps)))
                  shiftStates (deltaPop opa)
  in Set.size $ popStates `Set.union` (Set.fromList $ initials opa ++ finals opa)
