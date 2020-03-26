module POMC.Check ( State(..)
                  , closure
                  , atoms
                  , consistent
                  , showAtoms
                  , showStates
                  , check
                  ) where

import POMC.Opa (Prec(..), run)
import POMC.Potl
import POMC.Util (xor, implies)

import Data.Set (Set)
import qualified Data.Set as S

import Data.List (foldl')

-- TODO: remove
import qualified Debug.Trace as DT

closure :: Ord a => Formula a -> [Prop a] -> Set (Formula a)
closure phi otherProps = let propClos = concatMap (closList . Atomic) otherProps
                             phiClos  = closList phi
                         in S.fromList (propClos ++ phiClos)
  where
    chainNextExp pset g = concatMap (\p -> [ ChainNext (S.singleton p) g
                                           , Not (ChainNext (S.singleton p) g)
                                           ]) (S.toList pset)
    chainBackExp pset g = concatMap (\p -> [ ChainBack (S.singleton p) g
                                           , Not (ChainBack (S.singleton p) g)
                                           ]) (S.toList pset) ++
                          if Take `S.member` pset
                            then [ PrecBack (S.singleton Yield) g
                                 , Not (PrecBack (S.singleton Yield) g)
                                 , ChainBack (S.singleton Yield) g
                                 , Not (ChainBack (S.singleton Yield) g)
                                 ]
                            else []
    untilExp pset g h = [ PrecNext  pset (Until pset g h)
                        , Not $ PrecNext  pset (Until pset g h)
                        , ChainNext pset (Until pset g h)
                        , Not $ ChainNext pset (Until pset g h)
                        ] ++ chainNextExp pset (Until pset g h)
    closList f = case f of
      Atomic _         -> [f, Not f]
      Not g            -> [f] ++ closList g
      Or g h           -> [f, Not f] ++ closList g ++ closList h
      And g h          -> [f, Not f] ++ closList g ++ closList h
      PrecNext _ g     -> [f, Not f] ++ closList g
      PrecBack _ g     -> [f, Not f] ++ closList g
      ChainNext pset g -> [f, Not f] ++ closList g ++ chainNextExp pset g
      ChainBack pset g -> [f, Not f] ++ closList g ++ chainBackExp pset g
      Until pset g h   -> [f, Not f] ++ closList g ++ closList h ++ untilExp pset g h
      Since _ g h      -> [f, Not f] ++ closList g ++ closList h
      HierNext _ g     -> [f, Not f] ++ closList g
      HierBack _ g     -> [f, Not f] ++ closList g
      HierUntil _ g h  -> [f, Not f] ++ closList g ++ closList h
      HierSince _ g h  -> [f, Not f] ++ closList g ++ closList h

atoms :: Ord a => Set (Formula a) -> Set (Set (Formula a))
atoms clos = S.filter consistent .
             S.filter untilCons .
             S.filter chainNextCons .
             S.filter (complete clos) $ S.powerSet clos

complete :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
complete clos atom = all present clos
  where present nf@(Not f) = f `S.member` atom || nf      `S.member` atom
        present f          = f `S.member` atom || (Not f) `S.member` atom

consistent :: Ord a => Set (Formula a) -> Bool
consistent set = negcons set && andorcons set
  where negcons set   = True  `S.notMember` (S.map
                          (\f -> (negation f) `S.member` set
                          ) set)
        andorcons set = False `S.notMember` (S.map
                          (\f -> case f of
                            And g h -> g `S.member` set && h `S.member` set
                            Or  g h -> g `S.member` set || h `S.member` set
                            _       -> True
                          ) set)

chainNextCons :: Ord a => Set (Formula a) -> Bool
chainNextCons set = null [f | f@(ChainNext pset g) <- S.toList set,
                                                      S.size pset > 1 &&
                                                      not (valid pset g)]
  where valid pset g = any (\p -> ChainNext (S.singleton p) g `S.member` set)
                           (S.toList pset)

untilCons :: Ord a => Set (Formula a) -> Bool
untilCons set = null [f | f@(Until pset g h) <- S.toList set,
                                                not (valid f pset g h)]
  where valid u pset g h = (h `S.member` set) `xor`
                           ((S.fromList [g, PrecNext  pset u]) `S.isSubsetOf` set) `xor`
                           ((S.fromList [g, ChainNext pset u]) `S.isSubsetOf` set)

pendCombs clos =
  let cnfs = [f | f@(ChainNext pset _) <- S.toList clos, (S.size pset) == 1]
      cbfs = [f | f@(ChainBack pset _) <- S.toList clos, (S.size pset) == 1]
      cfset = S.fromList (cnfs ++ cbfs)
  in S.foldl S.union S.empty .
     S.map (S.fromList . combs) $
     S.powerSet cfset
  where
    combs atom = [(atom, xl, xr) | xl <- [False, True], xr <- [False, True]]

initials phi clos atoms =
  let compAtoms = S.filter (\atom ->  null [f | f@(PrecBack {}) <- S.toList atom]) .
                  S.filter (phi `S.member`) $
                  atoms
      cnyfSet = S.fromList [f | f@(ChainNext pset _) <- S.toList clos,
                                                        pset == (S.singleton Yield)]
  in [State ia ip True False | ia <- S.toList compAtoms,
                               ip <- S.toList (S.powerSet cnyfSet)]

atomicSet :: Set (Formula a) -> Set (Formula a)
atomicSet = S.filter atomic

showAtoms :: Show a => Set (Set (Formula a)) -> String
showAtoms = unlines . map (show . S.toList) . S.toList

showPendCombs :: Show a => Set ((Set (Formula a), Bool, Bool)) -> String
showPendCombs = unlines . map show . S.toList

data State a = State
    { current     :: Set (Formula a)
    , pending     :: Set (Formula a)
    , startsChain :: Bool
    , endsChain   :: Bool
    }

instance (Show a) => Show (State a) where
  show (State c p xl xr) = "\n{ C: "  ++ show (S.toList c)  ++
                           "\n, P: "  ++ show (S.toList p)  ++
                           "\n, XL: " ++ show xl            ++
                           "\n, XR: " ++ show xr            ++
                           "\n}"

showStates :: Show a => [State a] -> String
showStates = unlines . map show

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
      backfs   = map (\(f, p) -> f) precbacks
      precSets = map (\(f, p) -> p) precbacks

      atomProps = S.fromList [p | Atomic p <- S.toList atom]
      atomPrec = prec props atomProps

      fspresent = (S.fromList backfs) `S.isSubsetOf` (current s)
      rightprecs = all (atomPrec `S.member`) precSets
  in fspresent && rightprecs

deltaShift :: (Eq a, Ord a, Show a)
           => Set (Formula a)
           -> Set (Set (Formula a))
           -> Set (Set (Formula a), Bool, Bool)
           -> (Set (Prop a) -> Set (Prop a) -> Prec)
           -> State a
           -> Set (Prop a)
           -> [State a]
deltaShift clos atoms pends prec s props
  -- Shift rule
  | currAtomic /= S.map Atomic props = []

  -- XL rule
  | startsChain s = []

  -- ChainNext Equal rule 3
  | cneCheckSet /= S.fromList pendingSubCnefs = []
  -- ChainNext Take rule 3
  | not (null pendingCntfs) = []

  -- ChainBack Yield rule 2
  | not (null currCbyfs) = []
  -- ChainBack Equal rule 1
  | not (endsChain s) && not (null currCbefs) = []
  | endsChain s && (S.fromList currCbefs /= S.fromList pendingCbefs) = []
  -- ChainBack Take rule 2
  | not (endsChain s) && not (null currCbtfs) = []
  | endsChain s && (S.fromList currCbtfs /= S.fromList pendingCbtfs) = []

  | otherwise = debug ns
  where
    debug = id
    --debug = DT.trace ("\nShift with: " ++ show (S.toList props) ++
    --                  "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)

    -- ChainNext Yield formulas
    currCnyfs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Yield)]
    --  ChainNext Equal subformulas in the pending set
    pendingSubCnefs = [f | ChainNext pset f <- S.toList (pending s),
                                               pset == (S.singleton Equal)]
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- ChainNext Take formulas in the pending set
    pendingCntfs = [f | f@(ChainNext pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainNext Take formulas
    currCntfs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Take)]

    -- ChainBack Yield formulas
    currCbyfs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Yield)]
    -- ChainBack Yield formulas to be put in next pending set
    nextCbyfs = let cby = ChainBack (S.singleton Yield)
                in [cby f | f <- S.toList (current s), cby f `S.member` clos]
    -- ChainBack Equal formulas in the pending set
    pendingCbefs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Equal)]
    -- ChainBack Equal formulas
    currCbefs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- ChainBack Equal formulas to be put in next pending set
    nextCbefs = let cbe = ChainBack (S.singleton Equal)
                in [cbe f | f <- S.toList (current s), cbe f `S.member` clos]
    -- ChainBack Take formulas in the pending set
    pendingCbtfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainBack Take formulas
    currCbtfs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Take)]

    -- Fomulas that have a corresponding ChainNext Equal in the closure
    cneCheckSet = S.filter
                   (\f -> ChainNext (S.singleton Equal) f `S.member` clos)
                   (current s)

    -- Atoms compatible with PrecNext rule, PrecBack rule
    compAtoms = S.filter (precBackComp prec s props) .
                S.filter (precNextComp prec s props) $ atoms

    cnyComp (pend, xl, _) =
      let pendCnyfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Yield)]
      in (xl `implies` (S.fromList currCnyfs == S.fromList pendCnyfs)) &&
         ((not xl) `implies` (null currCnyfs))

    cneComp (pend, xl, _) =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in (xl `implies` (S.fromList currCnefs == S.fromList pendCnefs)) &&
         ((not xl) `implies` (null currCnefs))

    cntComp (pend, xl, _) =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in (xl `implies` (S.fromList currCntfs == S.fromList pendCntfs)) &&
         ((not xl) `implies` (null currCntfs))

    -- PrecNext formulas in the current set
    currPnfs = [f | f@(PrecNext _ _) <- S.toList (current s)]

    precNextComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          -- If a PrecNext has wrong precedence, then it does not belong to the
          -- current set
          precComp = null [f | f@(PrecNext pset _) <- currPnfs,
                                                      atomPrec `S.notMember` pset]

          -- Fromulas of the next atom which have a compatible PrecNext in the
          -- closure
          checkSet = atom `S.intersection`
                     S.fromList [sf | PrecNext pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]
          fsComp = S.fromList [sf | PrecNext _ sf <- currPnfs] == checkSet
      in precComp && fsComp

    cas = S.toList .
          S.filter (precBackComp prec s props) .
          S.filter precNextComp $ atoms

    cps = S.toList .
          S.filter cnyComp .
          S.filter cneComp .
          S.filter cntComp $ pends

    ns = [State c p xl xr | c <- cas, (p, xl, xr) <- cps]

deltaPush :: (Eq a, Ord a, Show a)
          => Set (Formula a)
          -> Set (Set (Formula a))
          -> Set (Set (Formula a), Bool, Bool)
          -> (Set (Prop a) -> Set (Prop a) -> Prec)
          -> State a
          -> Set (Prop a)
          -> [State a]
deltaPush clos atoms pends prec s props
  -- Push rule
  | currAtomic /= S.map Atomic props = []

  -- XL rule
  | not (startsChain s) = []

  -- ChainBack Yield rule 1
  | not (endsChain s) && not (null currCbyfs) = []
  | endsChain s && (S.fromList currCbyfs /= S.fromList pendingCbyfs) = []
  -- ChainBack Equal rule 2
  | not (null currCbefs) = []
  -- ChainBack Take rule 2
  | not (endsChain s) && not (null currCbtfs) = []
  | endsChain s && (S.fromList currCbtfs /= S.fromList pendingCbtfs) = []

  | otherwise = debug ns
  where
    debug = id
    -- debug = DT.trace ("\nPush with: " ++ show (S.toList props) ++
    --                   "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)

    -- ChainNext Yield formulas
    currCnyfs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Yield)]
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- ChainNext Take formulas
    currCntfs = [f | f@(ChainNext pset _) <- S.toList (current s),
                                             pset == (S.singleton Take)]

    -- ChainBack Yield formulas in the pending set
    pendingCbyfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Yield)]
    -- ChainBack Yield formulas
    currCbyfs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Yield)]
    -- ChainBack Yield formulas to be put in next pending set
    nextCbyfs = let cby = ChainBack (S.singleton Yield)
                in [cby f | f <- S.toList (current s), cby f `S.member` clos]
    -- ChainBack Equal formulas
    currCbefs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Equal)]
    -- ChainBack Equal formulas to be put in next pending set
    nextCbefs = let cbe = ChainBack (S.singleton Equal)
                in [cbe f | f <- S.toList (current s), cbe f `S.member` clos]
    -- ChainBack Take formulas in the pending set
    pendingCbtfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainBack Take formulas
    currCbtfs = [f | f@(ChainBack pset _) <- S.toList (current s),
                                             pset == (S.singleton Take)]

    cnyComp (pend, xl, _) =
      let pendCnyfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Yield)]
      in (xl `implies` (S.fromList currCnyfs == S.fromList pendCnyfs)) &&
         ((not xl) `implies` (null currCnyfs))

    cneComp (pend, xl, _) =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in (xl `implies` (S.fromList currCnefs == S.fromList pendCnefs)) &&
         ((not xl) `implies` (null currCnefs))

    cntComp (pend, xl, _) =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in (xl `implies` (S.fromList currCntfs == S.fromList pendCntfs)) &&
         ((not xl) `implies` (null currCntfs))

    -- PrecNext formulas in the current set
    currPnfs = [f | f@(PrecNext _ _) <- S.toList (current s)]

    precNextComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          -- If a PrecNext has wrong precedence, then it does not belong to the
          -- current set
          precComp = null [f | f@(PrecNext pset _) <- currPnfs,
                                                      atomPrec `S.notMember` pset]

          -- Fromulas of the next atom which have a compatible PrecNext in the
          -- closure
          checkSet = atom `S.intersection`
                     S.fromList [sf | PrecNext pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]
          fsComp = S.fromList [sf | PrecNext _ sf <- currPnfs] == checkSet
      in precComp && fsComp

    cas = S.toList .
          S.filter (precBackComp prec s props) .
          S.filter precNextComp $ atoms

    cps = S.toList .
          S.filter cnyComp .
          S.filter cneComp .
          S.filter cntComp $  pends

    ns = [State c p xl xr | c <- cas, (p, xl, xr) <- cps]

deltaPop :: (Eq a, Ord a, Show a)
         => Set (Formula a)
         -> Set (Set (Formula a))
         -> Set (Set (Formula a), Bool, Bool)
         -> (Set (Prop a) -> Set (Prop a) -> Prec)
         -> State a
         -> State a
         -> [State a]
deltaPop clos atoms pends prec s popped
  -- XL rule
  | startsChain s = []

  -- ChainNext Equal rule 2
  | not (null pendingCnefs) = []
  -- ChainNext Take rule 2
  | cntCheckSet /= S.fromList pendingSubCntfs = []

  | otherwise = debug ns

  -- concatMap (\a ->
  --   [ State a (pend `S.union` (S.fromList pendingCbtfs)) chainLeft True
  --   , State a (pend `S.union` (S.fromList nextPendCbtfs)) chainLeft False
  --   ]) . S.toList $ compAtoms

  where
    debug = id
    --debug = DT.trace ("\nPop with popped:\n" ++ show popped ++
    --                  "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId
    currAtomic = atomicSet (current s)

    -- ChainNext Equal formulas in the pending set
    pendingCnefs = [f | f@(ChainNext pset _) <- S.toList (pending s),
                                                pset == (S.singleton Equal)]
    -- ChainNext Take subformulas in the pending set
    pendingSubCntfs = [f | ChainNext pset f <- S.toList (pending s),
                                               pset == (S.singleton Take)]
    -- Fomulas that have a corresponding ChainNext Take in the closure
    cntCheckSet = S.filter
                   (\f -> ChainNext (S.singleton Take) f `S.member` clos)
                   (current s)

    -- Pending ChainNext Yield formulas of popped state
    poppedCnyfs = [f | f@(ChainNext pset _) <- S.toList (pending popped),
                                               pset == (S.singleton Yield)]
    -- Pending ChainNext Equal formulas of popped state
    poppedCnefs = [f | f@(ChainNext pset _) <- S.toList (pending popped),
                                               pset == (S.singleton Equal)]
    -- Pending ChainNext Take formulas of popped state
    poppedCntfs = [f | f@(ChainNext pset _) <- S.toList (pending popped),
                                               pset == (S.singleton Take)]

    -- ChainBack Yield formulas
    poppedCbyfs = [f | f@(ChainBack pset _) <- S.toList (pending popped),
                                               pset == (S.singleton Yield)]
    -- ChainBack Equal formulas
    poppedCbefs = [f | f@(ChainBack pset _) <- S.toList (pending popped),
                                               pset == (S.singleton Equal)]
    -- ChainBack Take formulas in the pending set
    pendingCbtfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainNext Yield formulas for next state's pending set when Xr is False
    nextPendCbtfs = let cbt = ChainBack (S.singleton Take)
                    in [cbt f | ChainBack pset f <- S.toList (current popped),
                                                    pset == (S.singleton Yield)
                                                    && cbt f `S.member` clos]
                       ++ [cbt f | PrecBack pset f <- S.toList (current popped),
                                                      pset == (S.singleton Yield)
                                                      && cbt f `S.member` clos]
                       ++ pendingCbtfs

    -- Is an atom compatible with pop rule?
    popComp atom = (S.filter atomic atom) == currAtomic
                   && (current s) `S.isSubsetOf` atom

    cnyComp (pend, xl, _) =
      let currCheckSet = S.map (ChainNext (S.singleton Yield)) .
                         S.filter (\f -> ChainNext (S.singleton Yield) f `S.member` clos) $
                         (current s)
          pendCheckSet = S.fromList [f | f@(ChainNext pset _) <- S.toList pend,
                                                                 pset == (S.singleton Yield)]
          checkSet = (currCheckSet `S.difference` pendCheckSet) `S.union`
                     (pendCheckSet `S.difference` currCheckSet)
      in (xl `implies` (S.fromList poppedCnyfs == checkSet)) &&
         ((not xl) `implies` (null poppedCnyfs))

    cneComp (pend, _, _) =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in S.fromList poppedCnefs == S.fromList pendCnefs

    cntComp (pend, _, _) =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in S.fromList poppedCntfs == S.fromList pendCntfs

    pendComp atom = cnyComp atom && cneComp atom && cntComp atom

    cas = S.toList . S.filter popComp $ atoms

    cps = S.toList . S.filter pendComp $ pends

    ns = [State c p xl xr | c <- cas, (p, xl, xr) <- cps]

isFinal :: (Show a) => State a -> Bool
isFinal s@(State c p xl xr) = debug $ not xl &&
                                      not xr &&
                                      S.null (pending s) &&
                                      S.null currAtomic &&
                                      S.null currFuture
  where currAtomic = S.filter atomic (current s)
        currFuture = S.filter future (current s)
        debug = id
        --debug = DT.trace ("\nIs state final?" ++ show s) . DT.traceShowId

check :: (Ord a, Show a)
      => Formula a
      -> (Set (Prop a) -> Set (Prop a) -> Prec)
      -> [Set (Prop a)]
      -> Bool
check phi prec ts =
  debug $ run
            prec
            is
            isFinal
            (deltaShift cl as pcs prec)
            (deltaPush  cl as pcs prec)
            (deltaPop   cl as pcs prec)
            ts
  where tsprops = S.toList $ foldl' (S.union) S.empty ts
        cl = closure phi tsprops
        as = atoms cl
        pcs = pendCombs cl
        is = initials phi cl as
        debug = DT.trace ("\nRun with:"         ++
                          "\nPhi:    "          ++ show phi          ++
                          "\nTokens: "          ++ show ts           ++
                          "\nToken props:\n"    ++ show tsprops      ++
                          "\nClosure:\n"        ++ show cl           ++
                          "\nAtoms:\n"          ++ showAtoms as      ++
                          "\nPending atoms:\n"  ++ showPendCombs pcs ++
                          "\nInitial states:\n" ++ showStates is)
