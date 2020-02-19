module POMC.Check ( closure
                  , atoms
                  , consistent
                  , complete
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

closure :: Ord a => Formula a -> [Prop a] -> Set (Formula a)
closure phi props = let propClos = concatMap (closList . Atomic) props
                        phiClos  = closList phi
                    in S.fromList (propClos ++ phiClos)
  where closList f = case f of
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
atoms clos = filterAtoms $ S.powerSet clos
  where filterAtoms = S.filter consistent . S.filter (complete clos)

consistent :: Ord a => Set (Formula a) -> Bool
consistent set = negcons set && andorcons set
  where
    negcons set   = True  `S.notMember` (S.map
                      (\f -> (negation f) `S.member` set
                      ) set)
    andorcons set = False `S.notMember` (S.map
                      (\f -> case f of
                        And g h -> g `S.member` set && h `S.member` set
                        Or  g h -> g `S.member` set || h `S.member` set
                        _       -> True
                      ) set)

complete :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
complete clos atom = all present clos
  where present nf@(Not f) = f `S.member` atom || nf      `S.member` atom
        present f          = f `S.member` atom || (Not f) `S.member` atom

data State a = State
    { current     :: Set (Formula a)
    , pending     :: Set (Formula a)
    , startsChain :: Bool
    }

instance (Show a) => Show (State a) where
  show (State c p xl) = "\n{ C: "  ++ show (S.toList c) ++
                        "\n, P: "  ++ show (S.toList p) ++
                        "\n, XL: " ++ show xl ++ "\n}"


emptyState = State S.empty S.empty False

defaultState atom = State atom S.empty False

chainLeftState currentAtom pendingAtom = State currentAtom pendingAtom True

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
precNextComp :: (Ord a)
                   => (Set (Prop a) -> Set (Prop a) -> Prec)
                   -> State a
                   -> Set (Prop a)
                   -> Set (Formula a)
                   -> Bool
precNextComp prec s props atom =
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
precBackComp :: (Ord a)
                   => (Set (Prop a) -> Set (Prop a) -> Prec)
                   -> State a
                   -> Set (Prop a)
                   -> Set (Formula a)
                   -> Bool
precBackComp prec s props atom =
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
deltaShift atoms prec s props
  -- Shift rule
  | currAtomic /= S.map Atomic props = []
  -- XL rule
  | startsChain s = []
  -- ChainNext Equal rule 3
  | not (all (`S.member` (current s)) pendingSubCnefs) = []
  -- If new pending set is empty, then we don't need XL. Correct??
  | null pend = debug $ map defaultState . S.toList $ compAtoms
  -- New pending set must be consistent
  | consistent pend = debug $ map ((flip chainLeftState) pend) . S.toList $ compAtoms
  | otherwise = []
  where
    debug = DT.trace ("\nShift with: " ++ show (S.toList props) ++
                      "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)
    --  ChainNext Equal subformulas in the pending set
    pendingSubCnefs = [f | ChainNext pset f <- S.toList (pending s),
                                               pset == (S.singleton Equal)]
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- Pending set for destination states. Constructed from:
    -- - ChainNext Equal rule 1
    pend = S.fromList currCnefs
    -- Atoms compatible with PrecNext rule, PrecBack rule
    compAtoms = S.filter (precBackComp prec s props) .
                S.filter (precNextComp prec s props) $ atoms

deltaPush :: (Eq a, Ord a, Show a)
          => Set (Set (Formula a))
          -> (Set (Prop a) -> Set (Prop a) -> Prec)
          -> State a
          -> Set (Prop a)
          -> [State a]
deltaPush atoms prec s props
  -- Push rule
  | currAtomic /= S.map Atomic props = []
  -- If new pending set is empty, then we don't need XL. Correct??
  | null pend = debug $ map defaultState . S.toList $ compAtoms
  -- New pending set must be consistent
  | consistent pend = debug $ map ((flip chainLeftState) pend) . S.toList $ compAtoms
  | otherwise = []
  where
    debug = DT.trace ("\nPush with: " ++ show (S.toList props) ++
                      "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- Pending set for destination states. Constructed from:
    -- - ChainNext Equal rule 1
    pend = S.fromList currCnefs
    -- Atoms compatible with PrecNext rule, PrecBack rule
    compAtoms = S.filter (precBackComp prec s props) .
                S.filter (precNextComp prec s props) $ atoms

deltaPop :: (Eq a, Ord a, Show a)
         => Set (Set (Formula a))
         -> (Set (Prop a) -> Set (Prop a) -> Prec)
         -> State a
         -> State a
         -> [State a]
deltaPop atoms prec s popped
  -- XL rule
  | startsChain s = []
  -- ChainNext Equal rule 2
  | not (null pendingCnefs) = []
  | consistent pend = debug $ map (\atom -> State atom pend False) . S.toList $ compAtoms
  | otherwise = []
  where
    debug = DT.trace ("\nPop with popped:\n" ++ show popped ++
                      "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)
    -- ChainNext Equal formulas in the pending set
    pendingCnefs = [f | f@(ChainNext pset _) <- S.toList (pending s),
                                            pset == (S.singleton Equal)]
    -- Pending ChainNext Equal formulas of popped state
    poppedCnefs = [f | f@(ChainNext pset _) <- S.toList (pending popped),
                                           pset == (S.singleton Equal)]
    -- Pending set for destination states. Constructed from:
    -- - ChainNext Equal rule 2
    pend = S.fromList poppedCnefs
    -- Pop rule
    popComp atom = (S.filter atomic atom) == currAtomic
                   && (current s) `S.isSubsetOf` atom
    compAtoms = S.filter popComp atoms

isFinal :: (Show a) => State a -> Bool
isFinal s =
  let currAtomic = S.filter atomic (current s)
  in DT.trace ("\nIs state final?" ++ show s) . DT.traceShowId $
     S.null currAtomic && S.null (pending s)

check :: (Ord a, Show a)
      => Formula a
      -> [Prop a]
      -> (Set (Prop a) -> Set (Prop a) -> Prec)
      -> [Set (Prop a)]
      -> Bool
check phi props prec ts =
  debug $ run prec is isFinal
    (deltaShift as prec) (deltaPush as prec) (deltaPop as prec) ts
  where as = atoms $ closure phi props
        initialAtoms = S.filter (phi `S.member`) as
        compatIas = S.filter (
                      \atom ->  null [f | f@(PrecBack {}) <- S.toList atom]
                      ) initialAtoms
        is = map defaultState $ S.toList compatIas
        debug = DT.trace ("\nRun with:\nPhi: " ++ show phi ++
                          "\nProps:" ++ show props ++
                          "\nAtoms:\n" ++ showAtoms as ++
                          "\nInitial states:\n" ++ showStates is)
