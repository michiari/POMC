module POMC.Check ( State(..)
                  , closure
                  , atoms
                  , showAtoms
                  , showStates
                  , check
                  ) where

import POMC.Opa (Prec(..), run)
import POMC.Potl
import POMC.Util (xor, implies)
import POMC.Data

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (foldl')

-- TODO: remove
import qualified Debug.Trace as DT

data Atom a = Atom
    { atomFormulaSet :: FormulaSet a
    , atomEncodedSet :: EncodedSet
    }

data State a = State
    { current   :: Atom a
    , pending   :: Set (Formula a)
    , mustPush  :: Bool
    , mustShift :: Bool
    , afterPop  :: Bool
    }

showFormulaSet :: (Show a) => FormulaSet a -> String
showFormulaSet fset = let fs = S.toList fset
                          posfs = filter (not . negative) fs
                          negfs = filter (negative) fs
                      in show (posfs ++ negfs)

instance (Show a) => Show (Atom a) where
  show (Atom fset eset) = "FS: " ++ showFormulaSet fset ++ "\t\tES: " ++ show eset

instance (Show a) => Show (State a) where
  show (State c p xl xe xr) = "\n{ C: "  ++ show c             ++
                              "\n, P: "  ++ show (S.toList p)  ++
                              "\n, XL: " ++ show xl            ++
                              "\n, X=: " ++ show xe            ++
                              "\n, XR: " ++ show xr            ++
                              "\n}"

showAtoms :: Show a => [Atom a] -> String
showAtoms = unlines . map show

showPendCombs :: Show a => Set ((Set (Formula a), Bool, Bool, Bool)) -> String
showPendCombs = unlines . map show . S.toList

showStates :: Show a => [State a] -> String
showStates = unlines . map show

atomicSet :: Set (Formula a) -> Set (Formula a)
atomicSet = S.filter atomic

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
                            then [ PrecBack  (S.singleton Yield) g
                                 , ChainBack (S.singleton Yield) g
                                 , Not $ PrecBack  (S.singleton Yield) g
                                 , Not $ ChainBack (S.singleton Yield) g
                                 ]
                            else []

    untilExp pset g h = [ PrecNext pset  (Until pset g h)
                        , ChainNext pset (Until pset g h)
                        , Not $ PrecNext  pset (Until pset g h)
                        , Not $ ChainNext pset (Until pset g h)
                        ] ++ chainNextExp pset (Until pset g h)
    sinceExp pset g h = [ PrecBack pset  (Since pset g h)
                        , ChainBack pset (Since pset g h)
                        , Not $ PrecBack  pset (Since pset g h)
                        , Not $ ChainBack pset (Since pset g h)
                        ] ++ chainBackExp pset (Since pset g h)

    hntExp g = [ ChainBack (S.singleton Yield) g
               , PrecBack  (S.singleton Yield) g
               , ChainBack (S.singleton Yield) (HierNextTake g)
               , PrecBack  (S.singleton Yield) (HierNextTake g)
               , Not $ ChainBack (S.singleton Yield) g
               , Not $ PrecBack  (S.singleton Yield) g
               , Not $ ChainBack (S.singleton Yield) (HierNextTake g)
               , Not $ PrecBack  (S.singleton Yield) (HierNextTake g)
               ]
    hbtExp g = [ ChainBack (S.singleton Yield) g
               , PrecBack  (S.singleton Yield) g
               , ChainBack (S.singleton Yield) (HierBackTake g)
               , PrecBack  (S.singleton Yield) (HierBackTake g)
               , Not $ ChainBack (S.singleton Yield) g
               , Not $ PrecBack  (S.singleton Yield) g
               , Not $ ChainBack (S.singleton Yield) (HierBackTake g)
               , Not $ PrecBack  (S.singleton Yield) (HierBackTake g)
               ]

    huyExp g h = [ T
                 , ChainBack (S.singleton Yield) T
                 , HierNextYield (HierUntilYield g h)
                 , Not $ T
                 , Not $ ChainBack (S.singleton Yield) T
                 , Not $ HierNextYield (HierUntilYield g h)
                 ]
    hsyExp g h = [ T
                 , ChainBack (S.singleton Yield) T
                 , HierBackYield (HierSinceYield g h)
                 , Not $ T
                 , Not $ ChainBack (S.singleton Yield) T
                 , Not $ HierBackYield (HierSinceYield g h)
                 ]
    hutExp g h = [ T
                 , ChainNext (S.singleton Take) T
                 , HierNextTake (HierUntilTake g h)
                 , Not $ T
                 , Not $ ChainNext (S.singleton Take) T
                 , Not $ HierNextTake (HierUntilTake g h)
                 ] ++ hntExp (HierUntilTake g h)
    hstExp g h = [ T
                 , ChainNext (S.singleton Take) T
                 , HierBackTake (HierSinceTake g h)
                 , Not $ T
                 , Not $ ChainNext (S.singleton Take) T
                 , Not $ HierBackTake (HierSinceTake g h)
                 ] ++ hbtExp (HierSinceTake g h)
    closList f = case f of
      T                  -> [f, Not f]
      Atomic _           -> [f, Not f]
      Not g              -> [f] ++ closList g
      Or g h             -> [f, Not f] ++ closList g ++ closList h
      And g h            -> [f, Not f] ++ closList g ++ closList h
      PrecNext _ g       -> [f, Not f] ++ closList g
      PrecBack _ g       -> [f, Not f] ++ closList g
      ChainNext pset g   -> [f, Not f] ++ closList g ++ chainNextExp pset g
      ChainBack pset g   -> [f, Not f] ++ closList g ++ chainBackExp pset g
      Until pset g h     -> [f, Not f] ++ closList g ++ closList h ++ untilExp pset g h
      Since pset g h     -> [f, Not f] ++ closList g ++ closList h ++ sinceExp pset g h
      HierNextYield g    -> [f, Not f] ++ closList g
      HierBackYield g    -> [f, Not f] ++ closList g
      HierNextTake  g    -> [f, Not f] ++ closList g ++ hntExp g
      HierBackTake  g    -> [f, Not f] ++ closList g ++ hbtExp g
      HierUntilYield g h -> [f, Not f] ++ closList g ++ closList h ++ huyExp g h
      HierSinceYield g h -> [f, Not f] ++ closList g ++ closList h ++ hsyExp g h
      HierUntilTake  g h -> [f, Not f] ++ closList g ++ closList h ++ hutExp g h
      HierSinceTake  g h -> [f, Not f] ++ closList g ++ closList h ++ hstExp g h

atoms :: Ord a => Set (Formula a) -> [Atom a]
atoms clos =
  let pclos = V.fromList (S.toAscList . S.filter (not . negative) $ clos)
      fetch i = pclos V.! i
      consistent fset = hierSinceTakeCons  clos fset &&
                        hierUntilTakeCons  clos fset &&
                        hierSinceYieldCons clos fset &&
                        hierUntilYieldCons clos fset &&
                        sinceCons          clos fset &&
                        untilCons          clos fset &&
                        chainBackCons      clos fset &&
                        chainNextCons      clos fset &&
                        orCons             clos fset &&
                        andCons            clos fset &&
                        tCons                   fset
      prependCons atoms eset = let fset = decode fetch eset
                               in if consistent fset
                                    then (Atom fset eset) : atoms
                                    else atoms
  in foldl' prependCons [] (generate $ V.length pclos)

tCons :: Ord a => Set (Formula a) -> Bool
tCons set = not (Not T `S.member` set)

andCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
andCons clos set = null [f | f@(And g h) <- S.toList set,
                                            not (g `S.member` set) ||
                                            not (h `S.member` set)]
                   &&
                   null [f | f@(And g h) <- S.toList clos,
                                            (g `S.member` set) &&
                                            (h `S.member` set) &&
                                            not (f `S.member` set)]

orCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
orCons clos set = null [f | f@(Or g h) <- S.toList set,
                                          not (g `S.member` set) &&
                                          not (h `S.member` set)]
                  &&
                  null [f | f@(Or g h) <- S.toList clos,
                                          ((g `S.member` set) ||
                                           (h `S.member` set)
                                          ) && not (f `S.member` set)]

chainNextCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
chainNextCons clos set = null [f | f@(ChainNext pset g) <- S.toList set,
                                                           S.size pset > 1 &&
                                                           not (present pset g)]
                         &&
                         null [f | f@(ChainNext pset g) <- S.toList clos,
                                                           S.size pset > 1 &&
                                                           present pset g &&
                                                           not (f `S.member` set)]
  where present pset g = any (\p -> ChainNext (S.singleton p) g `S.member` set)
                             (S.toList pset)

chainBackCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
chainBackCons clos set = null [f | f@(ChainBack pset g) <- S.toList set,
                                                           S.size pset > 1 &&
                                                           not (present pset g)]
                         &&
                         null [f | f@(ChainBack pset g) <- S.toList clos,
                                                           S.size pset > 1 &&
                                                           present pset g &&
                                                           not (f `S.member` set)]
  where present pset g = any (\p -> ChainBack (S.singleton p) g `S.member` set)
                             (S.toList pset)

untilCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
untilCons clos set = null [f | f@(Until pset g h) <- S.toList set,
                                                     not (present f pset g h)]
                     &&
                     null [f | f@(Until pset g h) <- S.toList clos,
                                                     present f pset g h &&
                                                     not (f `S.member` set)]
  where present u pset g h = (h `S.member` set) ||
                             ((S.fromList [g, PrecNext  pset u]) `S.isSubsetOf` set) ||
                             ((S.fromList [g, ChainNext pset u]) `S.isSubsetOf` set)

sinceCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
sinceCons clos set = null [f | f@(Since pset g h) <- S.toList set,
                                                     not (present f pset g h)]
                     &&
                     null [f | f@(Since pset g h) <- S.toList clos,
                                                     present f pset g h &&
                                                     not (f `S.member` set)]
  where present s pset g h = (h `S.member` set) ||
                             ((S.fromList [g, PrecBack  pset s]) `S.isSubsetOf` set) ||
                             ((S.fromList [g, ChainBack pset s]) `S.isSubsetOf` set)

hierUntilYieldCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
hierUntilYieldCons clos set = null [f | f@(HierUntilYield g h) <- S.toList set,
                                                                  not (present f g h)]
                              &&
                              null [f | f@(HierUntilYield g h) <- S.toList clos,
                                                                  present f g h &&
                                                                  not (f `S.member` set)]
  where present huy g h =
          ((S.fromList [h, ChainBack (S.singleton Yield) T]) `S.isSubsetOf` set) ||
          ((S.fromList [g, HierNextYield huy])               `S.isSubsetOf` set)

hierSinceYieldCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
hierSinceYieldCons clos set = null [f | f@(HierSinceYield g h) <- S.toList set,
                                                                  not (present f g h)]
                              &&
                              null [f | f@(HierSinceYield g h) <- S.toList clos,
                                                                  present f g h &&
                                                                  not (f `S.member` set)]
  where present hsy g h =
          ((S.fromList [h, ChainBack (S.singleton Yield) T]) `S.isSubsetOf` set) ||
          ((S.fromList [g, HierBackYield hsy])               `S.isSubsetOf` set)

hierUntilTakeCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
hierUntilTakeCons clos set = null [f | f@(HierUntilTake g h) <- S.toList set,
                                                                not (present f g h)]
                             &&
                             null [f | f@(HierUntilTake g h) <- S.toList clos,
                                                                present f g h &&
                                                                not (f `S.member` set)]
  where present hut g h =
          ((S.fromList [h, ChainNext (S.singleton Take) T]) `S.isSubsetOf` set) ||
          ((S.fromList [g, HierNextTake hut])               `S.isSubsetOf` set)

hierSinceTakeCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
hierSinceTakeCons clos set = null [f | f@(HierSinceTake g h) <- S.toList set,
                                                                not (present f g h)]
                             &&
                             null [f | f@(HierSinceTake g h) <- S.toList clos,
                                                                present f g h &&
                                                                not (f `S.member` set)]
  where present hst g h =
          ((S.fromList [h, ChainNext (S.singleton Take) T]) `S.isSubsetOf` set) ||
          ((S.fromList [g, HierBackTake hst])               `S.isSubsetOf` set)

pendCombs :: (Ord a) => Set (Formula a) -> Set ((Set (Formula a), Bool, Bool, Bool))
pendCombs clos =
  let cnfs  = [f | f@(ChainNext pset _) <- S.toList clos, (S.size pset) == 1]
      cbfs  = [f | f@(ChainBack pset _) <- S.toList clos, (S.size pset) == 1]
      hnyfs = [f | f@(HierNextYield _) <- S.toList clos]
      hntfs = [f | f@(HierNextTake _)  <- S.toList clos]
      hbtfs = [f | f@(HierBackTake _)  <- S.toList clos]
  in S.foldl' S.union S.empty .
     S.map (S.fromList . combs) $
     S.powerSet (S.fromList $ cnfs ++ cbfs ++ hnyfs ++ hntfs ++ hbtfs)
  where
    combs atom = [(atom, xl, xe, xr) | xl <- [False, True],
                                       xe <- [False, True],
                                       xr <- [False, True]]

initials :: (Ord a) => Formula a -> FormulaSet a -> [Atom a] -> [State a]
initials phi clos atoms =
  let compatible atom = let fset = atomFormulaSet atom
                        in phi `S.member` fset &&
                           null [f | f@(PrecBack {}) <- S.toList fset]
      compAtoms = filter compatible atoms
      cnyfSet = S.fromList [f | f@(ChainNext pset _) <- S.toList clos,
                                                        pset == (S.singleton Yield)]
  in [State ia ip True False False | ia <- compAtoms,
                                     ip <- S.toList (S.powerSet cnyfSet)]

deltaShift :: (Eq a, Ord a, Show a)
           => Set (Formula a)
           -> [Atom a]
           -> Set (Set (Formula a), Bool, Bool, Bool)
           -> (Set (Prop a) -> Set (Prop a) -> Prec)
           -> State a
           -> Set (Prop a)
           -> [State a]
deltaShift clos atoms pends prec s props
  -- Shift rule
  | currAtomic /= S.map Atomic props = []

  -- XL rule
  | mustPush s = []
  -- XE rule
  | not (mustShift s) = []

  -- ChainNext Equal rule 3
  | cneCheckSet /= S.fromList pendingSubCnefs = []
  -- ChainNext Take rule 3
  | not (null pendingCntfs) = []

  -- ChainBack Yield rule 2
  | not (null currCbyfs) = []
  -- ChainBack Equal rule 1
  | not (afterPop s) && not (null currCbefs) = []
  | afterPop s && (S.fromList currCbefs /= S.fromList pendingCbefs) = []
  -- ChainBack Take rule 2
  | not (afterPop s) && not (null currCbtfs) = []
  | afterPop s && (S.fromList currCbtfs /= S.fromList pendingCbtfs) = []

  -- HierNextYield rule 5
  | not (null currHnyfs) || not (null pendingHnyfs) = []

  -- HierBackTake rule 5
  | not (null pendingHbtfs) = []

  | otherwise = debug ns
  where
    debug = id
    --debug = DT.trace ("\nShift with: " ++ show (S.toList props) ++
    --                  "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId

    currFset = atomFormulaSet (current s)

    currAtomic = atomicSet currFset

    --  ChainNext Equal subformulas in the pending set
    pendingSubCnefs = [f | ChainNext pset f <- S.toList (pending s),
                                               pset == (S.singleton Equal)]
    -- ChainNext Take formulas in the pending set
    pendingCntfs = [f | f@(ChainNext pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- Fomulas that have a corresponding ChainNext Equal in the closure
    cneCheckSet = S.filter
                   (\f -> ChainNext (S.singleton Equal) f `S.member` clos)
                   currFset

    -- ChainNext Yield formulas
    currCnyfs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Yield)]
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Equal)]
    -- ChainNext Take formulas
    currCntfs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Take)]

    -- ChainBack Yield formulas
    currCbyfs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Yield)]
    -- ChainBack Equal formulas
    currCbefs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Equal)]
    -- ChainBack Equal formulas in the pending set
    pendingCbefs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Equal)]
    -- ChainBack Take formulas in the pending set
    pendingCbtfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainBack Take formulas
    currCbtfs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Take)]

    -- Hierarchical Next Yield formulas
    currHnyfs = [f | f@(HierNextYield _) <- S.toList currFset]
    -- Pending Hierarchical Next Yield formulas
    pendingHnyfs = [f | f@(HierNextYield _) <- S.toList (pending s)]

    -- Hierarchical Back Take formulas
    pendingHbtfs = [f | f@(HierBackTake _) <- S.toList (pending s)]

    cnyComp pend xl =
      let pendCnyfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Yield)]
      in (xl `implies` (S.fromList currCnyfs == S.fromList pendCnyfs)) &&
         ((not xl) `implies` (null currCnyfs))

    cneComp pend xl =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in (xl `implies` (S.fromList currCnefs == S.fromList pendCnefs)) &&
         ((not xl) `implies` (null currCnefs))

    cntComp pend xl =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in (xl `implies` (S.fromList currCntfs == S.fromList pendCntfs)) &&
         ((not xl) `implies` (null currCntfs))

    cbyComp pend =
      let pendSubCbyfs = [sf | ChainBack pset sf <- S.toList pend,
                                                    pset == (S.singleton Yield)]
          checkSet = S.filter
                       (\f -> ChainBack (S.singleton Yield) f `S.member` clos)
                       currFset
      in S.fromList pendSubCbyfs == checkSet

    cbeComp pend =
      let pendSubCbefs = [sf | ChainBack pset sf <- S.toList pend,
                                                    pset == (S.singleton Equal)]
          checkSet = S.filter
                       (\f -> ChainBack (S.singleton Equal) f `S.member` clos)
                       currFset
      in S.fromList pendSubCbefs == checkSet

    cbtComp pend =
      let pendCbtfs = [f | f@(ChainBack pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in null pendCbtfs

    hntComp pend xl =
      let pendHntfs = [f | f@(HierNextTake _) <- S.toList pend]
          currHntfs = [f | f@(HierNextTake _) <- S.toList currFset]
      in null pendHntfs && (not (null currHntfs) `implies` xl)

    hbtComp pend xl =
      let currHbtfs = [f | f@(HierBackTake _) <- S.toList currFset]
      in if not (null currHbtfs)
           then xl
           else True

    pendComp (pend, xl, xe, xr) = not xr &&
                                  cnyComp pend xl &&
                                  cneComp pend xl &&
                                  cntComp pend xl &&
                                  cbyComp pend &&
                                  cbeComp pend &&
                                  cbtComp pend &&
                                  hntComp pend xl &&
                                  hbtComp pend xl

    -- PrecNext formulas in the current set
    currPnfs = [f | f@(PrecNext _ _) <- S.toList currFset]

    precNextComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          -- If a PrecNext concerns incompatible precedences, then it does not
          -- belong to the current set
          precComp = null [f | f@(PrecNext pset _) <- currPnfs,
                                                      atomPrec `S.notMember` pset]

          -- Formulas of the next atom which have a compatible PrecNext in the
          -- closure
          checkSet = atom `S.intersection`
                     S.fromList [sf | PrecNext pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]
          fsComp = S.fromList [sf | PrecNext _ sf <- currPnfs] == checkSet
      in precComp && fsComp

    precBackComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          atomPbfs = [f | f@(PrecBack _ _) <- S.toList atom]

          -- If a PrecBack concerns incompatible precedences, then it does not
          -- belong to the atom
          precComp = null [f | f@(PrecBack pset _) <- atomPbfs,
                                                      atomPrec `S.notMember` pset]

          -- Formulas in the current set which have a compatible PrecBack in the
          -- closure
          checkSet = currFset `S.intersection`
                     S.fromList [sf | PrecBack pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]

          fsComp = checkSet == S.fromList [sf | PrecBack _ sf <- atomPbfs]
      in precComp && fsComp

    cas = filter (\(Atom fset eset) -> precBackComp fset &&
                                       precNextComp fset
                 ) atoms

    cps = S.toList . S.filter pendComp $ pends

    ns = [State c p xl xe xr | c <- cas, (p, xl, xe, xr) <- cps]

deltaPush :: (Eq a, Ord a, Show a)
          => Set (Formula a)
          -> [Atom a]
          -> Set (Set (Formula a), Bool, Bool, Bool)
          -> (Set (Prop a) -> Set (Prop a) -> Prec)
          -> State a
          -> Set (Prop a)
          -> [State a]
deltaPush clos atoms pends prec s props
  -- Push rule
  | currAtomic /= S.map Atomic props = []

  -- XL rule
  | not (mustPush s) = []
  -- XE rule
  | mustShift s = []

  -- ChainBack Yield rule 1
  | not (afterPop s) && not (null currCbyfs) = []
  | afterPop s && (S.fromList currCbyfs /= S.fromList pendingCbyfs) = []
  -- ChainBack Equal rule 2
  | not (null currCbefs) = []
  -- ChainBack Take rule 2
  | not (afterPop s) && not (null currCbtfs) = []
  | afterPop s && (S.fromList currCbtfs /= S.fromList pendingCbtfs) = []

  -- HierNextYield rule 1
  | not (afterPop s) && not (null currHnyfs) = []
  -- HierNextYield rule 2
  | not (afterPop s) && not (null pendingSubHnyfs) = []
  | afterPop s && hnyCheckSet /= S.fromList pendingSubHnyfs = []

  -- HierBackYield rule 1
  | not (null currHbyfs) && not (mustPush s && afterPop s) = []

  -- HierBackTake rule 5
  | not (null pendingHbtfs) = []

  | otherwise = debug ns
  where
    debug = id
    --debug = DT.trace ("\nPush with: " ++ show (S.toList props) ++
    --                  "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId

    currFset = atomFormulaSet (current s)

    currAtomic = atomicSet currFset

    -- ChainNext Yield formulas
    currCnyfs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Yield)]
    -- ChainNext Equal formulas
    currCnefs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Equal)]
    -- ChainNext Take formulas
    currCntfs = [f | f@(ChainNext pset _) <- S.toList currFset,
                                             pset == (S.singleton Take)]

    -- ChainBack Yield formulas in the pending set
    pendingCbyfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Yield)]
    -- ChainBack Yield formulas
    currCbyfs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Yield)]
    -- ChainBack Equal formulas
    currCbefs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Equal)]
    -- ChainBack Take formulas in the pending set
    pendingCbtfs = [f | f@(ChainBack pset _) <- S.toList (pending s),
                                                pset == (S.singleton Take)]
    -- ChainBack Take formulas
    currCbtfs = [f | f@(ChainBack pset _) <- S.toList currFset,
                                             pset == (S.singleton Take)]

    -- Hierarchical Next Yield formulas
    currHnyfs = [f | f@(HierNextYield _) <- S.toList currFset]
    -- Pending Hierarchical Next Yield subformulas
    pendingSubHnyfs = [g | HierNextYield g <- S.toList (pending s)]
    -- Fomulas that have a corresponding Hierarchical Next Yield in the closure
    hnyCheckSet = S.filter
                   (\f -> HierNextYield f `S.member` clos)
                   currFset

    -- Hierarchical Back Yield formulas
    currHbyfs = [f | f@(HierBackYield _) <- S.toList currFset]

    -- Hierarchical Back Take formulas
    pendingHbtfs = [f | f@(HierBackTake _) <- S.toList (pending s)]

    cnyComp pend xl =
      let pendCnyfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Yield)]
      in (xl `implies` (S.fromList currCnyfs == S.fromList pendCnyfs)) &&
         ((not xl) `implies` (null currCnyfs))

    cneComp pend xl =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in (xl `implies` (S.fromList currCnefs == S.fromList pendCnefs)) &&
         ((not xl) `implies` (null currCnefs))

    cntComp pend xl =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in (xl `implies` (S.fromList currCntfs == S.fromList pendCntfs)) &&
         ((not xl) `implies` (null currCntfs))

    cbyComp pend =
      let pendSubCbyfs = [sf | ChainBack pset sf <- S.toList pend,
                                                    pset == (S.singleton Yield)]
          checkSet = S.filter
                       (\f -> ChainBack (S.singleton Yield) f `S.member` clos)
                       currFset
      in S.fromList pendSubCbyfs == checkSet

    cbeComp pend =
      let pendSubCbefs = [sf | ChainBack pset sf <- S.toList pend,
                                                    pset == (S.singleton Equal)]
          checkSet = S.filter
                       (\f -> ChainBack (S.singleton Equal) f `S.member` clos)
                       currFset
      in S.fromList pendSubCbefs == checkSet

    cbtComp pend =
      let pendCbtfs = [f | f@(ChainBack pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in null pendCbtfs

    hntComp pend xl =
      let pendHntfs = [f | f@(HierNextTake _) <- S.toList pend]
          currHntfs = [f | f@(HierNextTake _) <- S.toList currFset]
      in null pendHntfs && (not (null currHntfs) `implies` xl)

    hbtComp pend xl =
      let currHbtfs = [f | f@(HierBackTake _) <- S.toList currFset]
      in if not (null currHbtfs)
           then xl
           else True

    pendComp (pend, xl, xe, xr) = not xr &&
                                  cnyComp pend xl &&
                                  cneComp pend xl &&
                                  cntComp pend xl &&
                                  cbyComp pend &&
                                  cbeComp pend &&
                                  cbtComp pend &&
                                  hntComp pend xl &&
                                  hbtComp pend xl

    -- PrecNext formulas in the current set
    currPnfs = [f | f@(PrecNext _ _) <- S.toList currFset]

    precNextComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          -- If a PrecNext concerns incompatible precedences, then it does not
          -- belong to the current set
          precComp = null [f | f@(PrecNext pset _) <- currPnfs,
                                                      atomPrec `S.notMember` pset]

          -- Formulas of the next atom which have a compatible PrecNext in the
          -- closure
          checkSet = atom `S.intersection`
                     S.fromList [sf | PrecNext pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]
          fsComp = S.fromList [sf | PrecNext _ sf <- currPnfs] == checkSet
      in precComp && fsComp

    precBackComp atom =
      let atomProps = S.fromList [p | Atomic p <- S.toList atom]
          atomPrec = prec props atomProps

          atomPbfs = [f | f@(PrecBack _ _) <- S.toList atom]

          -- If a PrecBack concerns incompatible precedences, then it does not
          -- belong to the atom
          precComp = null [f | f@(PrecBack pset _) <- atomPbfs,
                                                      atomPrec `S.notMember` pset]

          -- Formulas in the current set which have a compatible PrecBack in the
          -- closure
          checkSet = currFset `S.intersection`
                     S.fromList [sf | PrecBack pset sf <- S.toList clos,
                                                          atomPrec `S.member` pset]

          fsComp = checkSet == S.fromList [sf | PrecBack _ sf <- atomPbfs]
      in precComp && fsComp

    cas = filter (\(Atom fset eset) -> precBackComp fset &&
                                       precNextComp fset
                 ) atoms

    cps = S.toList . S.filter pendComp $ pends

    ns = [State c p xl xe xr | c <- cas, (p, xl, xe, xr) <- cps]

deltaPop :: (Eq a, Ord a, Show a)
         => Set (Formula a)
         -> [Atom a]
         -> Set (Set (Formula a), Bool, Bool, Bool)
         -> (Set (Prop a) -> Set (Prop a) -> Prec)
         -> State a
         -> State a
         -> [State a]
deltaPop clos atoms pends prec s popped
  -- XL rule
  | mustPush s = []
  -- XE rule
  | mustShift s = []

  -- ChainNext Equal rule 2
  | not (null pendingCnefs) = []
  -- ChainNext Take rule 2
  | cntCheckSet /= S.fromList pendingSubCntfs = []

  -- HierNextYield rule 4
  | not (null pendingHnyfs) = []

  | otherwise = debug ns
  where
    debug = id
    --debug = DT.trace ("\nPop with popped:\n" ++ show popped ++
    --                  "\nFrom:\n" ++ show s ++ "\nResult:") . DT.traceShowId

    currFset = atomFormulaSet (current s)
    poppedCurrFset = atomFormulaSet (current popped)

    currAtomic = atomicSet currFset

    -- ChainNext Equal formulas in the pending set
    pendingCnefs = [f | f@(ChainNext pset _) <- S.toList (pending s),
                                                pset == (S.singleton Equal)]
    -- ChainNext Take subformulas in the pending set
    pendingSubCntfs = [f | ChainNext pset f <- S.toList (pending s),
                                               pset == (S.singleton Take)]
    -- Fomulas that have a corresponding ChainNext Take in the closure
    cntCheckSet = S.filter
                   (\f -> ChainNext (S.singleton Take) f `S.member` clos)
                   currFset

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

    -- Pending Hierarchical Next Yield formulas
    pendingHnyfs = [f | f@(HierNextYield _) <- S.toList (pending s)]

    -- Is an atom compatible with pop rule?
    popComp atom = atomEncodedSet (current s) == atomEncodedSet atom

    cnyComp pend xl =
      let currCheckSet = S.map (ChainNext (S.singleton Yield)) .
                         S.filter (\f -> ChainNext (S.singleton Yield) f `S.member` clos) $
                         currFset
          pendCheckSet = S.fromList [f | f@(ChainNext pset _) <- S.toList pend,
                                                                 pset == (S.singleton Yield)]
          checkSet = (currCheckSet `S.difference` pendCheckSet) `S.union`
                     (pendCheckSet `S.difference` currCheckSet)
      in (xl `implies` (S.fromList poppedCnyfs == checkSet)) &&
         ((not xl) `implies` (null poppedCnyfs))

    cneComp pend =
      let pendCnefs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in S.fromList poppedCnefs == S.fromList pendCnefs

    cntComp pend =
      let pendCntfs = [f | f@(ChainNext pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
      in S.fromList poppedCntfs == S.fromList pendCntfs

    cbyComp pend =
      let pendCbyfs = [f | f@(ChainBack pset _) <- S.toList pend,
                                                   pset == (S.singleton Yield)]
      in S.fromList poppedCbyfs == S.fromList pendCbyfs

    cbeComp pend =
      let pendCbefs = [f | f@(ChainBack pset _) <- S.toList pend,
                                                   pset == (S.singleton Equal)]
      in S.fromList poppedCbefs == S.fromList pendCbefs

    cbtComp pend xl xe =
      let pendCbtfs = [f | f@(ChainBack pset _) <- S.toList pend,
                                                   pset == (S.singleton Take)]
          -- These definitions could be moved out
          cbt f = ChainBack (S.singleton Take) f
          yieldCheckSet = S.fromList
                           [cbt f | ChainBack pset f <- S.toList poppedCurrFset,
                                                        pset == (S.singleton Yield)
                                                        && cbt f `S.member` clos]
                          `S.union`
                          S.fromList
                            [cbt f | PrecBack pset f <- S.toList poppedCurrFset,
                                                        pset == (S.singleton Yield)
                                                        && cbt f `S.member` clos]
          takeCheckSet = S.fromList pendingCbtfs
          checkSet = yieldCheckSet `S.union` takeCheckSet
      in if (xl || xe)
           then S.fromList pendingCbtfs == S.fromList pendCbtfs
           else checkSet == S.fromList pendCbtfs

    hnyComp pend xr =
      let pendHnyfs = [f | f@(HierNextYield _) <- S.toList pend]
          poppedCurrHnyfs = [f | f@(HierNextYield _) <- S.toList poppedCurrFset]
      in if afterPop popped
           then S.fromList poppedCurrHnyfs == S.fromList pendHnyfs
           else True

    hntComp pend xl xe =
      let cby f = ChainBack (S.singleton Yield) f
          pby f = PrecBack (S.singleton Yield) f
          pendSubHntfs = [g | HierNextTake g <- S.toList pend]
          pendingSubHntfs = [g | HierNextTake g <- S.toList (pending s)]
          pendCheckList = [g | HierNextTake g <- S.toList clos,
                                                 cby g `S.member` poppedCurrFset ||
                                                 pby g `S.member` poppedCurrFset]
          pendingCheckList = [g | f@(HierNextTake g) <- S.toList clos,
                                                        cby f `S.member` poppedCurrFset ||
                                                        pby f `S.member` poppedCurrFset]
      in if not xl
         then (S.fromList pendCheckList == S.fromList pendSubHntfs) &&
              (S.fromList pendingSubHntfs == S.fromList pendingCheckList)
         else True

    hbtComp pend xl xe =
      let cby f = ChainBack (S.singleton Yield) f
          pby f = PrecBack (S.singleton Yield) f

          pendSubHbtfs = [g | HierBackTake g <- S.toList pend]
          pendingSubHbtfs = [g | HierBackTake g <- S.toList (pending s)]

          pendCheckList = [g | f@(HierBackTake g) <- S.toList clos,
                                                     cby f `S.member` poppedCurrFset ||
                                                     pby f `S.member` poppedCurrFset]
          pendingCheckList = [g | HierBackTake g <- S.toList clos,
                                                    cby g `S.member` poppedCurrFset ||
                                                    pby g `S.member` poppedCurrFset]
      in (not (null pendingSubHbtfs) `implies` (not xl && not xe)) &&
         (not xl `implies` ((S.fromList pendCheckList == S.fromList pendSubHbtfs) &&
                            (S.fromList pendingSubHbtfs == S.fromList pendingCheckList)))

    pendComp (pend, xl, xe, xr) = xr &&
                                  cnyComp pend xl &&
                                  cneComp pend &&
                                  cntComp pend &&
                                  cbyComp pend &&
                                  cbeComp pend &&
                                  cbtComp pend xl xe &&
                                  hnyComp pend xr &&
                                  hntComp pend xl xe &&
                                  hbtComp pend xl xe

    cas = filter popComp atoms

    cps = S.toList . S.filter pendComp $ pends

    hbyCombComp curr xl =
      let nextSubHbyfs = [g | HierBackYield g <- S.toList curr]
          poppedCurrSubHbyfSet = S.filter
                                   (\f -> HierBackYield f `S.member` clos) $
                                   poppedCurrFset
      in if xl
           then if afterPop popped
                  then S.fromList nextSubHbyfs == poppedCurrSubHbyfSet
                  else null nextSubHbyfs
           else True

    ns = [State c p xl xe xr | c <- cas, (p, xl, xe, xr) <- cps,
                               hbyCombComp (atomFormulaSet c) xl]

isFinal :: (Show a) => State a -> Bool
isFinal s@(State c p xl xe xr) = debug $ not xl &&
                                         not xe &&
                                         S.null currAtomic &&
                                         S.null currFuture &&
                                         pendComb
  where currFset = atomFormulaSet (current s)
        currAtomic = S.filter atomic currFset
        currFuture = S.filter future currFset
        pendComb = all (\f -> case f of  -- only ChainBack Take formulas are allowed
                                ChainBack pset _ -> pset == S.singleton Take
                                _ -> False
                       ) (S.toList $ pending s)
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
  where nphi = normalize phi
        tsprops = S.toList $ foldl' (S.union) S.empty ts
        cl = closure nphi tsprops
        as = atoms cl
        pcs = pendCombs cl
        is = initials nphi cl as
        debug = DT.trace ("\nRun with:"         ++
                          "\nPhi:          "    ++ show phi          ++
                          "\nNorm. phi:    "    ++ show nphi         ++
                          "\nTokens:       "    ++ show ts           ++
                          "\nToken props:\n"    ++ show tsprops      ++
                          "\nClosure:\n"        ++ showFormulaSet cl ++
                          "\nAtoms:\n"          ++ showAtoms as      ++
                          "\nPending atoms:\n"  ++ showPendCombs pcs ++
                          "\nInitial states:\n" ++ showStates is)
