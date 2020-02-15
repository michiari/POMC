module POMC.Check ( clos
                  , atoms
                  , consistent
                  , showAtoms
                  , showStates
                  , State(..)
                  , check
                  ) where

import POMC.Opa (Prec(..), run)
import POMC.Potl

import Data.Set (Set)
import qualified Data.Set as S

-- TODO: remove
import qualified Debug.Trace as DT

clos :: Ord a => Formula a -> [Prop a] -> Set (Formula a)
clos phi props = let propClos = concatMap (\p -> closList $ Atomic p) props
                     phiClos  = closList phi
                 in S.fromList (propClos ++ phiClos)
                 where
                   closList f = case f of
                     Atomic _        -> [f, Not f]
                     Not g           -> [f] ++ closList g
                     Or g h          -> [f, Not f] ++ closList g ++ closList h
                     And g h         -> [f, Not f] ++ closList g ++ closList h
                     PrecNext _ g    -> [f, Not f] ++ closList g
                     PrecBack _ g    -> [f, Not f] ++ closList g
                     ChainNext _ g   -> [f, Not f] ++ closList g
                     ChainBack _ g   -> [f, Not f] ++ closList g
                     Until _ g h     -> [f, Not f] ++ closList g ++ closList h
                     Since _ g h     -> [f, Not f] ++ closList g ++ closList h
                     HierNext _ g    -> [f, Not f] ++ closList g
                     HierBack _ g    -> [f, Not f] ++ closList g
                     HierUntil _ g h -> [f, Not f] ++ closList g ++ closList h
                     HierSince _ g h -> [f, Not f] ++ closList g ++ closList h

atoms :: Ord a => Set (Formula a) -> Set (Set (Formula a))
atoms = S.filter consistent . S.powerSet

consistent :: Ord a => Set (Formula a) -> Bool
consistent atom = negcons atom && andorcons atom
  where
    negcons atom   = True  `S.notMember` (S.map
                       (\f -> (negation f) `S.member` atom
                       ) atom)
    andorcons atom = False `S.notMember` (S.map
                       (\f -> case f of
                         And g h -> g `S.member` atom && h `S.member` atom
                         Or  g h -> g `S.member` atom || h `S.member` atom
                         _       -> True
                       ) atom)

data State a = State
    { current :: Set (Formula a)
    , pending :: Set (Formula a)
    }

instance (Show a) => Show (State a) where
  show (State c p) = "\n{ C: "  ++ show (S.toList c) ++
                     "\n, P: " ++ show (S.toList p) ++ "\n}"

emptyState = State S.empty S.empty

atomicSet :: Set (Formula a) -> Set (Formula a)
atomicSet = S.filter atomic

showAtoms :: Show a => Set (Set (Formula a)) -> String
showAtoms = unlines . map (show . S.toList) . S.toList

showStates :: Show a => [State a] -> String
showStates = unlines . map show

-- Checks if an atom is compatible (reachable with a shift/push move) with
-- current state s w.r.t. PrecNext formulas contained in s.
--
-- For every PrecNext[PI](f) belonging to s, we check that:
-- - f is present in the atom
-- - pi belongs to PI, where pi is the precedence relation between current
--   input propositions and the atomic set of the atom
precNextCompatible :: (Ord a)
                   => (Set (Prop a) -> Set (Prop a) -> Prec)
                   -> State a
                   -> Set (Prop a)
                   -> Set (Formula a)
                   -> Bool
precNextCompatible prec s props atom =
  let precnexts = [(f,pset) | PrecNext pset f <- S.toList (current s)]
      nextfs = map (\(f, p) -> f) precnexts
      precSets = map (\(f, p) -> p) precnexts

      atomProps = S.fromList [p | Atomic p <- S.toList atom]
      atomPrec = prec props atomProps

      fspresent = (S.fromList nextfs) `S.isSubsetOf` atom
      rightprecs = all (atomPrec `S.member`) precSets
  in fspresent && rightprecs

-- Checks if an atom is compatible (reachable with a shift/push move) with
-- current state s w.r.t. PrecBack formulas contained in the atom.
--
-- For every PrecBack[PI](f) belonging to the atom, we check that:
-- - f is present in s
-- - pi belongs to PI, where pi is the precedence relation between current
--   input propositions and the atomic set of the atom
precBackCompatible :: (Ord a)
                   => (Set (Prop a) -> Set (Prop a) -> Prec)
                   -> State a
                   -> Set (Prop a)
                   -> Set (Formula a)
                   -> Bool
precBackCompatible prec s props atom =
  let precbacks = [(f,pset) | PrecBack pset f <- S.toList atom]
      backfs = map (\(f, p) -> f) precbacks
      precSets = map (\(f, p) -> p) precbacks

      atomProps = S.fromList [p | Atomic p <- S.toList atom]
      atomPrec = prec props atomProps

      fspresent = (S.fromList backfs) `S.isSubsetOf` (current s)
      rightprecs = all (atomPrec `S.member`) precSets
  in fspresent && rightprecs

deltaShift :: (Eq a, Ord a, Show a)
           => Set (Set (Formula a))
           -> (Set (Prop a) -> Set (Prop a) -> Prec)
           -> State a
           -> Set (Prop a)
           -> [State a]
deltaShift atoms prec s props =
  let currAtomic = atomicSet (current s)
  in DT.trace ("\nShift with: " ++ show (S.toList props) ++
               "\nFrom:\n" ++ show s ++ "\nResult:") $ DT.traceShowId $
     if currAtomic == S.map Atomic props
       then map
              (\a -> State a (pending s))
              (S.toList $
                S.filter (precBackCompatible prec s props) $
                  S.filter (precNextCompatible prec s props) atoms)
       else []

deltaPush :: (Eq a, Ord a, Show a)
          => Set (Set (Formula a))
          -> (Set (Prop a) -> Set (Prop a) -> Prec)
          -> State a
          -> Set (Prop a)
          -> [State a]
deltaPush atoms prec s props =
  let currAtomic = atomicSet (current s)
  in DT.trace ("\nPush with: " ++ show (S.toList props) ++
               "\nFrom:\n" ++ show s ++ "\nResult:") $ DT.traceShowId $
     if currAtomic == S.map Atomic props
       then map
              (\a -> State a (pending s))
              (S.toList $
                S.filter (precBackCompatible prec s props) $
                  S.filter (precNextCompatible prec s props) atoms)
       else []

deltaPop :: (Eq a, Ord a, Show a)
         => Set (Set (Formula a))
         -> (Set (Prop a) -> Set (Prop a) -> Prec)
         -> State a
         -> State a
         -> [State a]
deltaPop atoms prec s popped =
  let currAtomic = atomicSet (current s)
      compatible atom = (S.filter atomic atom) == currAtomic
                        && (current s) `S.isSubsetOf` atom
  in DT.trace ("\nPop with popped:\n" ++ show popped ++
               "\nFrom:\n" ++ show s ++ "\nResult:") $ DT.traceShowId $
     map (\at -> State at (pending s)) $ S.toList $ S.filter compatible atoms

isFinal :: (Show a) => State a -> Bool
isFinal s =
  let currAtomic = S.filter atomic (current s)
  in DT.trace ("\nIs state final?" ++ show s) $ DT.traceShowId $
     S.null currAtomic && S.null (pending s)

check :: (Ord a, Show a)
      => Formula a
      -> [Prop a]
      -> (Set (Prop a) -> Set (Prop a) -> Prec)
      -> [Set (Prop a)]
      -> Bool
check phi props prec ts =
  let as = atoms $ clos phi props
      initialAtoms = S.filter (phi `S.member`) as
      compatIas = S.filter (
                    \atom ->  null [f | f@(PrecBack {}) <- S.toList atom]
                    ) initialAtoms
      is = map (\s -> State s S.empty) $ S.toList compatIas
  in DT.trace ("\nRun with:\nPhi: " ++ show phi ++ "\nProps:" ++ show props ++
               "\nAtoms:\n" ++ showAtoms as ++
               "\nInitial states:\n" ++ showStates is) $
     run prec is isFinal
         (deltaShift as prec) (deltaPush as prec) (deltaPop as prec) ts
