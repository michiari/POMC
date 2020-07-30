{-# LANGUAGE DeriveGeneric #-}

module Pomc.ModelChecker (
                           ExplicitOpa(..)
                         , modelCheck
                         , modelCheckGen
                         ) where

import Pomc.Prop (Prop)
import Pomc.Prec (StructPrecRel)
import Pomc.RPotl (Formula(..))
import Pomc.Check (Checkable(..), State, makeOpa)
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
  { sigma :: ([Prop a], [Prop a])
  , precRel :: [StructPrecRel a]
  , initials   :: [s]
  , finals     :: [s]
  , deltaPush  :: [(s, Set (Prop a), [s])]
  , deltaShift :: [(s, Set (Prop a), [s])]
  , deltaPop   :: [(s, s, [s])]
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

modelCheck :: (Checkable f, Ord s, Hashable s, Show s)
           => f APType
           -> ExplicitOpa s APType
           -> Bool
modelCheck phi opa =
  let (bitenc, precFunc, phiInitials, phiIsFinal, phiDeltaPush, phiDeltaShift, phiDeltaPop) =
        makeOpa (Not . toReducedPotl $ phi) (sigma opa) (precRel opa)

      cInitials = cartesian (initials opa) phiInitials
      cIsFinal (MCState q p) = Set.member q (Set.fromList $ finals opa) && phiIsFinal p

      maybeList Nothing = []
      maybeList (Just l) = l

      makeDeltaMapI delta = Map.fromList $
        map (\(q', b', ps) -> ((q', D.encodeInput bitenc b'), ps)) delta
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

modelCheckGen :: (Checkable f, Ord s, Hashable s, Show s, Ord a)
              => f a
              -> ExplicitOpa s a
              -> Bool
modelCheckGen phi opa =
  let (sls, als) = sigma opa
      (tphi, tprec, trans) = convAP (toReducedPotl phi) (precRel opa) (sls ++ als)
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
