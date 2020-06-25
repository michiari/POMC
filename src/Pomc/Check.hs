{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Check
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Check ( -- * Checking functions
                    check
                  , fastcheck
                    -- * Checking typeclass
                  , Checkable(..)
                    -- * Checking helpers
                  , closure
                    -- * Printing
                  , showAtoms
                  , showStates
                  , Atom(..)
                  , State(..)
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..))
import Pomc.Opa (run, augRun)
import Pomc.RPotl (Formula(..), negative, atomic, normalize, future)
import Pomc.Util (xor, implies, safeHead)
import Pomc.Data (encode, decodeAtom, generate, FormulaSet, EncodedSet)

import Data.Maybe (fromJust, fromMaybe)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Vector.Unboxed as VU

import Data.List (foldl')

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad (guard, filterM)

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Data.Hashable

import qualified Data.Sequence as SQ

import Data.Foldable (toList)

-- TODO: remove
import qualified Debug.Trace as DT

class Checkable c where
  toReducedPotl :: c a -> Formula a

instance Checkable (Formula) where
  toReducedPotl = id

data Atom a = Atom
    { atomFormulaSet :: FormulaSet a
    , atomEncodedSet :: EncodedSet
    , atomHash       :: Int
    } deriving (Generic, NFData)

data State a = State
    { current   :: Atom a
    , pending   :: Set (Formula a)
    , mustPush  :: Bool
    , mustShift :: Bool
    , afterPop  :: Bool
    , stateHash :: Int
    } deriving (Generic, NFData, Ord, Eq)

-- Make things Hashable
instance Hashable a => Hashable (Atom a) where
  hashWithSalt salt atom = hashWithSalt salt (atomHash atom)

instance Hashable a => Hashable (State a) where
  hashWithSalt salt state = hashWithSalt salt (stateHash state)

hashState :: (Hashable a) => Atom a -> Set (Formula a) -> Bool -> Bool -> Bool -> Int
hashState c p mp ms ap =
  (hash c) `hashWithSalt`
  p `hashWithSalt`
  mp `hashWithSalt`
  ms `hashWithSalt` ap

instance Eq (Atom a) where
  p == q = (atomEncodedSet p) == (atomEncodedSet q)

instance Ord (Atom a) where
  compare p q = compare (atomEncodedSet p) (atomEncodedSet q)

showFormulaSet :: (Show a) => FormulaSet a -> String
showFormulaSet fset = let fs = S.toList fset
                          posfs = filter (not . negative) fs
                          negfs = filter (negative) fs
                      in show (posfs ++ negfs)

instance (Show a) => Show (Atom a) where
  show (Atom fset eset _) = "FS: " ++ showFormulaSet fset ++ "\t\tES: " ++ show eset

instance (Show a) => Show (State a) where
  show (State c p xl xe xr _) = "\n{ C: "  ++ show c             ++
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

compProps :: (Eq a, Ord a) => Set (Formula a) -> Set (Prop a) -> Bool
compProps fset pset = atomicSet fset == S.map Atomic pset

closure :: Ord a => Formula a -> [Prop a] -> Set (Formula a)
closure phi otherProps = let propClos = concatMap (closList . Atomic) (End : otherProps)
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

    hntExp g = [ HierTakeHelper g
               , HierTakeHelper (HierNextTake g)
               , Not $ HierTakeHelper g
               , Not $ HierTakeHelper (HierNextTake g)
               ]
    hbtExp g = [ HierTakeHelper g
               , HierTakeHelper (HierBackTake g)
               , Not $ HierTakeHelper g
               , Not $ HierTakeHelper (HierBackTake g)
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
    evExp g = [ PrecNext (S.fromList [Yield, Equal, Take]) (Eventually' g)
              , Not $ PrecNext (S.fromList [Yield, Equal, Take]) (Eventually' g)
              ]
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
      HierTakeHelper g   -> [f, Not f] ++ closList g
      Eventually' g      -> [f, Not f] ++ closList g ++ evExp g

atoms :: Ord a => Set (Formula a) -> Set (Set (Prop a)) -> [Atom a]
atoms clos inputSet =
  let validPropSets = S.insert (S.singleton End) inputSet

      atomics = map makeCouples . map (S.map Atomic) $ S.toList validPropSets
        where makeCouples aset = let easet = encode atomicLookup (S.size pAtomicClos) aset
                                     aset' = decodeAtom (fetch pAtomicVec) easet
                                 in (aset', easet)

      pclos = S.filter (not . negative) clos

      pProplessClos = S.filter (not . atomic) pclos
      pFormulaVec = V.fromList . S.toAscList $ pProplessClos

      pAtomicClos = S.filter (atomic) pclos
      pAtomicVec = V.fromList . S.toAscList $ pAtomicClos
      atomicLookup phi = fromJust (M.lookup phi atomicMap)
        where atomicMap = M.fromAscList (zip (S.toAscList pAtomicClos) [0..])

      fetch vec i = vec V.! i

      checks =
        [ onlyif (T `S.member` clos) trueCons
        , onlyif (not . null $ [f | f@(And _ _)            <- cl]) (andCons clos)
        , onlyif (not . null $ [f | f@(Or _ _)             <- cl]) (orCons clos)
        , onlyif (not . null $ [f | f@(ChainNext _ _)      <- cl]) (chainNextCons clos)
        , onlyif (not . null $ [f | f@(ChainBack _ _)      <- cl]) (chainBackCons clos)
        , onlyif (not . null $ [f | f@(Until _ _ _)        <- cl]) (untilCons clos)
        , onlyif (not . null $ [f | f@(Since _ _ _)        <- cl]) (sinceCons clos)
        , onlyif (not . null $ [f | f@(HierUntilYield _ _) <- cl]) (hierUntilYieldCons clos)
        , onlyif (not . null $ [f | f@(HierSinceYield _ _) <- cl]) (hierSinceYieldCons clos)
        , onlyif (not . null $ [f | f@(HierUntilTake _ _)  <- cl]) (hierUntilTakeCons clos)
        , onlyif (not . null $ [f | f@(HierSinceTake _ _)  <- cl]) (hierSinceTakeCons clos)
        , onlyif (not . null $ [f | f@(Eventually' _)      <- cl]) (evCons clos)
        ]
        where onlyif cond f = if cond then f else const True
              cl = S.toList clos
      consistent fset = all (\c -> c fset) checks

      prependCons as eset =
        let fset = decodeAtom (fetch pFormulaVec) eset
            combs = do (aset, easet) <- atomics
                       let fset' = fset `S.union` aset
                           eset' = easet VU.++ eset
                       guard (consistent fset')
                       return (Atom fset' eset' $ hash eset')
        in as SQ.>< (SQ.fromList combs)
  in toList $ foldl' prependCons SQ.empty (generate $ V.length pFormulaVec)

atomicCons :: Ord a => (Set (Prop a) -> Bool) -> Set (Formula a) -> Bool
atomicCons valid set =
  let propSet = S.fromList [p | Atomic p <- S.toList set]
      size = S.size propSet
  in (End `S.member` propSet) `implies` (size == 1) && valid propSet

trueCons :: Ord a => Set (Formula a) -> Bool
trueCons set = not (Not T `S.member` set)

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

evCons :: Ord a => Set (Formula a) -> Set (Formula a) -> Bool
evCons clos set = null [f | f@(Eventually' g) <- S.toList set,
                                                 not (present f g)]
                  &&
                  null [f | f@(Eventually' g) <- S.toList clos,
                                                 present f g &&
                                                 not (f `S.member` set)]
  where present ev g =
          (g `S.member` set) ||
          (PrecNext (S.fromList [Yield, Equal, Take]) ev `S.member` set)

pendCombs :: (Ord a) => Set (Formula a) -> Set ((Set (Formula a), Bool, Bool, Bool))
pendCombs clos =
  let cnfs  = [f | f@(ChainNext pset _) <- S.toList clos, (S.size pset) == 1]
      cbfs  = [f | f@(ChainBack pset _) <- S.toList clos, (S.size pset) == 1]
      hnyfs = [f | f@(HierNextYield _)  <- S.toList clos]
      hntfs = [f | f@(HierNextTake _)   <- S.toList clos]
      hbtfs = [f | f@(HierBackTake _)   <- S.toList clos]
      hthfs = [f | f@(HierTakeHelper _) <- S.toList clos]
  in S.foldl' S.union S.empty .
     S.map (S.fromList . combs) $
     S.powerSet (S.fromList $ cnfs ++ cbfs ++ hnyfs ++ hntfs ++ hbtfs ++ hthfs)
  where
    combs atom = [(atom, xl, xe, xr) | xl <- [False, True],
                                       xe <- [False, True],
                                       xr <- [False, True],
                                       not (xl && xe)]

initials :: (Ord a, Hashable a) => Formula a -> FormulaSet a -> [Atom a] -> [State a]
initials phi clos atoms =
  let compatible atom = let fset = atomFormulaSet atom
                        in phi `S.member` fset &&
                           null [f | f@(PrecBack {}) <- S.toList fset]
      compAtoms = filter compatible atoms
      cnyfSet = S.fromList [f | f@(ChainNext pset _) <- S.toList clos,
                                                        pset == (S.singleton Yield)]
  in [State ia ip True False False (hashState ia ip True False False) |
      ia <- compAtoms,
      ip <- S.toList (S.powerSet cnyfSet)]

resolve :: i -> [(i -> Bool, b)] -> [b]
resolve info conditionals = snd . unzip $ filter (\(cond, _) -> cond info) conditionals

deltaRules :: (Show a, Ord a) => Set (Formula a) -> (RuleGroup a, RuleGroup a, RuleGroup a)
deltaRules condInfo =
  let shiftGroup = RuleGroup
        { ruleGroupPrs  = resolve condInfo [ (const True, xlShiftPr)
                                           , (const True, xeShiftPr)
                                           , (const True, propShiftPr)
                                           , (cneCond,    cneShiftPr)
                                           , (cntCond,    cntShiftPr)
                                           , (cbyCond,    cbyShiftPr)
                                           , (cbeCond,    cbeShiftPr)
                                           , (cbtCond,    cbtShiftPr)
                                           , (hnyCond,    hnyShiftPr)
                                           , (hbyCond,    hbyShiftPr)
                                           , (hbtCond,    hbtShiftPr)
                                           , (hthCond,    hthShiftPr)
                                           ]
        , ruleGroupFcrs = resolve condInfo [ (pnCond, pnShiftFcr)
                                           , (pbCond, pbShiftFcr)
                                           ]
        , ruleGroupFprs = resolve condInfo [ (const True, xrShiftFpr)
                                           , (cnyCond,    cnyShiftFpr)
                                           , (cneCond,    cneShiftFpr)
                                           , (cntCond,    cntShiftFpr)
                                           , (cbyCond,    cbyShiftFpr)
                                           , (cbeCond,    cbeShiftFpr)
                                           , (cbtCond,    cbtShiftFpr)
                                           , (hntCond,    hntShiftFpr1)
                                           , (hntCond,    hntShiftFpr2)
                                           , (hbtCond,    hbtShiftFpr)
                                           , (hthCond,    hthShiftFpr)
                                           ]
        , ruleGroupFrs  = resolve condInfo []
        }
      pushGroup = RuleGroup
        { ruleGroupPrs  = resolve condInfo [ (const True, xlPushPr)
                                           , (const True, xePushPr)
                                           , (const True, propPushPr)
                                           , (cbyCond,    cbyPushPr)
                                           , (cbeCond,    cbePushPr)
                                           , (cbtCond,    cbtPushPr)
                                           , (hnyCond,    hnyPushPr1)
                                           , (hnyCond,    hnyPushPr2)
                                           , (hbyCond,    hbyPushPr)
                                           , (hbtCond,    hbtPushPr)
                                           , (hthCond,    hthPushPr)
                                           ]
        , ruleGroupFcrs = resolve condInfo [ (pnCond, pnPushFcr)
                                           , (pbCond, pbPushFcr)
                                           ]
        , ruleGroupFprs = resolve condInfo [ (const True, xrPushFpr)
                                           , (cnyCond,    cnyPushFpr)
                                           , (cneCond,    cnePushFpr)
                                           , (cntCond,    cntPushFpr)
                                           , (cbyCond,    cbyPushFpr)
                                           , (cbeCond,    cbePushFpr)
                                           , (cbtCond,    cbtPushFpr)
                                           , (hntCond,    hntPushFpr1)
                                           , (hntCond,    hntPushFpr2)
                                           , (hbtCond,    hbtPushFpr)
                                           , (hthCond,    hthPushFpr)
                                           ]
        , ruleGroupFrs  = resolve condInfo []
        }
      popGroup = RuleGroup
        { ruleGroupPrs  = resolve condInfo [ (const True, xlPopPr)
                                           , (const True, xePopPr)
                                           , (cneCond,    cnePopPr)
                                           , (cntCond,    cntPopPr)
                                           , (hnyCond,    hnyPopPr)
                                           ]
        , ruleGroupFcrs = resolve condInfo [(const True, currPopFcr)]
        , ruleGroupFprs = resolve condInfo [ (const True, xrPopFpr)
                                           , (cnyCond,    cnyPopFpr)
                                           , (cneCond,    cnePopFpr)
                                           , (cntCond,    cntPopFpr)
                                           , (cbyCond,    cbyPopFpr)
                                           , (cbeCond,    cbePopFpr)
                                           , (cbtCond,    cbtPopFpr)
                                           , (hnyCond,    hnyPopFpr)
                                           , (hntCond,    hntPopFpr1)
                                           , (hntCond,    hntPopFpr2)
                                           , (hntCond,    hntPopFpr3)
                                           , (hbtCond,    hbtPopFpr1)
                                           , (hbtCond,    hbtPopFpr2)
                                           , (hbtCond,    hbtPopFpr3)
                                           , (hthCond,    hthPopFpr)
                                           ]
        , ruleGroupFrs  = resolve condInfo [(hbyCond, hbyPopFr)]
        }
  in (shiftGroup, pushGroup, popGroup)
  where
    -- XL rules
    xlShiftPr info = let pXl = mustPush (prState info) in not pXl
    xlPushPr  info = let pXl = mustPush (prState info) in pXl
    xlPopPr   info = let pXl = mustPush (prState info) in not pXl
    --

    -- XE rules
    xeShiftPr info = let pXe = mustShift (prState info) in pXe
    xePushPr  info = let pXe = mustShift (prState info) in not pXe
    xePopPr   info = let pXe = mustShift (prState info) in not pXe
    --

    -- XR rules
    xrShiftFpr info = let (_, _, _, fXr) = fprFuturePendComb info in not fXr
    xrPushFpr  info = let (_, _, _, fXr) = fprFuturePendComb info in not fXr
    xrPopFpr   info = let (_, _, _, fXr) = fprFuturePendComb info in fXr
    --

    -- Prop rules
    propPushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          props = fromJust (prProps info)
      in compProps pCurr props

    propShiftPr = propPushPr
    --

    -- Pop rule
    currPopFcr info =
      let pEncCurr = atomEncodedSet . current $ fcrState info
          fEncCurr = atomEncodedSet (fcrFutureCurr info)
      in pEncCurr == fEncCurr
    --

    -- PN rules
    pnCond clos = not (null [f | f@(PrecNext _ _) <- S.toList clos])

    pnPushFcr info =
      let clos = fcrClos info
          pCurr = atomFormulaSet . current $ fcrState info
          precFunc = fcrPrecFunc info
          props = fromJust (fcrProps info)
          fCurr = atomFormulaSet (fcrFutureCurr info)

          pCurrPnfs = [f | f@(PrecNext _ _) <- S.toList pCurr]

          fCurrProps = S.fromList [p | Atomic p <- S.toList fCurr]

          precComp prec = null [f | f@(PrecNext pset _) <- pCurrPnfs,
                                                           prec `S.notMember` pset]

          fsComp prec = S.fromList pCurrPnfs == checkSet
            where checkSet = S.fromList
                               [f | f@(PrecNext pset g) <- S.toList clos,
                                                           prec `S.member` pset &&
                                                           g `S.member` fCurr]
      in case precFunc props fCurrProps of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pnShiftFcr = pnPushFcr
    --

    -- PB rules
    pbCond clos = not (null [f | f@(PrecBack _ _) <- S.toList clos])

    pbPushFcr info =
      let clos = fcrClos info
          pCurr = atomFormulaSet . current $ fcrState info
          precFunc = fcrPrecFunc info
          props = fromJust (fcrProps info)
          fCurr = atomFormulaSet (fcrFutureCurr info)

          fCurrPbfs = [f | f@(PrecBack _ _) <- S.toList fCurr]

          fCurrProps = S.fromList [p | Atomic p <- S.toList fCurr]

          precComp prec = null [f | f@(PrecBack pset _) <- fCurrPbfs,
                                                           prec `S.notMember` pset]

          fsComp prec = S.fromList fCurrPbfs == checkSet
            where checkSet = S.fromList
                               [f | f@(PrecBack pset g) <- S.toList clos,
                                                           prec `S.member` pset &&
                                                           g `S.member` pCurr]
      in case precFunc props fCurrProps of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pbShiftFcr = pbPushFcr
    --

    -- CNY
    cnyCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == S.singleton Yield])

    cnyPushFpr info =
      let pCurr = atomFormulaSet . current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          pCurrCnyfs = [f | f@(ChainNext pset _) <- S.toList pCurr,
                                                    pset == S.singleton Yield]
          fPendCnyfs = [f | f@(ChainNext pset _) <- S.toList fPend,
                                                    pset == S.singleton Yield]
      in if fXl
           then S.fromList pCurrCnyfs == S.fromList fPendCnyfs
           else null pCurrCnyfs

    cnyShiftFpr = cnyPushFpr

    cnyPopFpr info =
      let clos = fprClos info
          pCurr = atomFormulaSet . current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          ppPend = pending $ fromJust (fprPopped info)
          ppPendCnyfs = [f | f@(ChainNext pset _) <- S.toList ppPend,
                                                     pset == S.singleton Yield]
          pCheckSet = S.fromList [f | f@(ChainNext pset g) <- S.toList clos,
                                                              pset == S.singleton Yield &&
                                                              g `S.member` pCurr]
          fCheckSet = S.fromList [f | f@(ChainNext pset _) <- S.toList fPend,
                                                              pset == S.singleton Yield]
          checkSet = pCheckSet `S.union` fCheckSet
      in if fXl
           then S.fromList ppPendCnyfs == checkSet
           else null ppPendCnyfs
    --

    -- CNE rules
    cneCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == S.singleton Equal])

    cnePushFpr info =
      let pCurr = atomFormulaSet . current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCnefs = [f | f@(ChainNext pset _) <- S.toList fPend,
                                                    pset == S.singleton Equal]
          pCurrCnefs = [f | f@(ChainNext pset _) <- S.toList pCurr,
                                                    pset == S.singleton Equal]
      in if fXl
           then S.fromList pCurrCnefs == S.fromList fPendCnefs
           else null pCurrCnefs

    cneShiftFpr = cnePushFpr

    cnePopPr info =
      let pPend = pending (prState info)
          pPendCnefs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Equal]
      in null pPendCnefs

    cnePopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCnefs = [f | f@(ChainNext pset _) <- S.toList ppPend,
                                                     pset == S.singleton Equal]
          fPendCnefs = [f | f@(ChainNext pset _) <- S.toList fPend,
                                                    pset == S.singleton Equal]
      in S.fromList ppPendCnefs == S.fromList fPendCnefs

    cneShiftPr info =
      let clos = prClos info
          pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pPendCnefs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Equal]
          pCheckList = [f | f@(ChainNext pset g) <- S.toList clos,
                                                    pset == S.singleton Equal,
                                                    g `S.member` pCurr]
      in S.fromList pCheckList == S.fromList pPendCnefs
    --

    -- CNT rules
    cntCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == S.singleton Take])

    cntPushFpr info =
      let pCurr = atomFormulaSet . current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCntfs = [f | f@(ChainNext pset _) <- S.toList fPend,
                                                    pset == S.singleton Take]
          pCurrCntfs = [f | f@(ChainNext pset _) <- S.toList pCurr,
                                                    pset == S.singleton Take]
      in if fXl
           then S.fromList pCurrCntfs == S.fromList fPendCntfs
           else null pCurrCntfs

    cntShiftFpr = cntPushFpr

    cntPopPr info =
      let clos = prClos info
          pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pPendCntfs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Take]
          pCheckList = [f | f@(ChainNext pset g) <- S.toList clos,
                                                    pset == S.singleton Take,
                                                    g `S.member` pCurr]
      in S.fromList pCheckList == S.fromList pPendCntfs

    cntPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCntfs = [f | f@(ChainNext pset _) <- S.toList ppPend,
                                                     pset == S.singleton Take]
          fPendCntfs = [f | f@(ChainNext pset _) <- S.toList fPend,
                                                    pset == S.singleton Take]
      in S.fromList ppPendCntfs == S.fromList fPendCntfs

    cntShiftPr info =
      let pPend = pending (prState info)
          pPendCntfs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Take]
      in null pPendCntfs
    --

    -- CBY
    cbyCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == S.singleton Yield])

    cbyPushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbyfs = [f | f@(ChainBack pset _) <- S.toList pCurr,
                                                    pset == S.singleton Yield]
          pPendCbyfs = [f | f@(ChainBack pset _) <- S.toList pPend,
                                                    pset == S.singleton Yield]
      in if pXr
           then S.fromList pCurrCbyfs == S.fromList pPendCbyfs
           else null pCurrCbyfs

    cbyShiftPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pCurrCbyfs = [f | f@(ChainBack pset _) <- S.toList pCurr,
                                                    pset == S.singleton Yield]
      in null pCurrCbyfs

    cbyPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCbyfs = [f | f@(ChainBack pset _) <- S.toList ppPend,
                                                     pset == S.singleton Yield]
          fPendCbyfs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Yield]
      in S.fromList ppPendCbyfs == S.fromList fPendCbyfs

    cbyPushFpr info =
      let clos = fprClos info
          pCurr = atomFormulaSet . current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendCbyfs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Yield]
          pCheckSet = S.fromList [f | f@(ChainBack pset g) <- S.toList clos,
                                                              pset == S.singleton Yield &&
                                                              g `S.member` pCurr]
      in S.fromList fPendCbyfs == pCheckSet

    cbyShiftFpr = cbyPushFpr
    --

    -- CBE
    cbeCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == S.singleton Equal])

    cbeShiftPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbefs = [f | f@(ChainBack pset _) <- S.toList pCurr,
                                                    pset == S.singleton Equal]
          pPendCbefs = [f | f@(ChainBack pset _) <- S.toList pPend,
                                                    pset == S.singleton Equal]
      in if pXr
           then S.fromList pCurrCbefs == S.fromList pPendCbefs
           else null pCurrCbefs

    cbePushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pCurrCbefs = [f | f@(ChainBack pset _) <- S.toList pCurr,
                                                    pset == S.singleton Equal]
      in null pCurrCbefs

    cbePopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCbefs = [f | f@(ChainBack pset _) <- S.toList ppPend,
                                                     pset == S.singleton Equal]
          fPendCbefs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Equal]
      in S.fromList ppPendCbefs == S.fromList fPendCbefs

    cbePushFpr info =
      let clos = fprClos info
          pCurr = atomFormulaSet . current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info

          fPendCbefs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Equal]
          pCheckSet = S.fromList [f | f@(ChainBack pset g) <- S.toList clos,
                                                              pset == S.singleton Equal &&
                                                              g `S.member` pCurr]
      in S.fromList fPendCbefs == pCheckSet

    cbeShiftFpr = cbePushFpr
    --

    -- CBT
    cbtCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == S.singleton Take])

    cbtPushFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info
          fPendCbtfs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Take]
      in null fPendCbtfs

    cbtShiftFpr = cbtPushFpr

    cbtPushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbtfs = [f | f@(ChainBack pset _) <- S.toList pCurr,
                                                    pset == S.singleton Take]
          pPendCbtfs = [f | f@(ChainBack pset _) <- S.toList pPend,
                                                    pset == S.singleton Take]
      in if pXr
           then S.fromList pCurrCbtfs == S.fromList pPendCbtfs
           else null pCurrCbtfs

    cbtShiftPr = cbtPushPr

    cbtPopFpr info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (fPend, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)
          pPendCbtfs = [f | f@(ChainBack pset _) <- S.toList pPend,
                                                    pset == S.singleton Take]
          fPendCbtfs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Take]
          cbt f = ChainBack (S.singleton Take) f
          yieldCheckSet = S.fromList
                           [cbt f | ChainBack pset f <- S.toList ppCurr,
                                                        pset == (S.singleton Yield)
                                                        && cbt f `S.member` clos]
                          `S.union`
                          S.fromList
                            [cbt f | PrecBack pset f <- S.toList ppCurr,
                                                        pset == (S.singleton Yield)
                                                        && cbt f `S.member` clos]
          takeCheckSet = S.fromList pPendCbtfs
          checkSet = yieldCheckSet `S.union` takeCheckSet
      in if fXl || fXe
           then S.fromList pPendCbtfs == S.fromList fPendCbtfs
           else checkSet == S.fromList fPendCbtfs
    --

    -- HNY
    hnyCond clos = not (null [f | f@(HierNextYield _) <- S.toList clos])

    hnyPushPr1 info =
      let pCurr = atomFormulaSet . current $ prState info
          pXr = afterPop (prState info)
          pCurrHnyfs = [f | f@(HierNextYield _) <- S.toList pCurr]
      in if not (null pCurrHnyfs)
           then pXr
           else True

    hnyPushPr2 info =
      let clos = prClos info
          pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pPendHnyfs = [f | f@(HierNextYield _) <- S.toList pPend]
          checkSet = S.fromList [f | f@(HierNextYield g) <- S.toList clos,
                                                            g `S.member` pCurr]
      in if pXr
           then checkSet == S.fromList pPendHnyfs
           else null pPendHnyfs

    hnyPopFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)
          ppXr = afterPop $ fromJust (fprPopped info)
          fPendHnyfs = [f | f@(HierNextYield _) <- S.toList fPend]
          ppCurrHnyfs = [f | f@(HierNextYield _) <- S.toList ppCurr]
      in if ppXr
           then S.fromList ppCurrHnyfs == S.fromList fPendHnyfs
           else True

    hnyPopPr info =
      let pPend = pending (prState info)
          pPendHnyfs = [f | f@(HierNextYield _) <- S.toList pPend]
      in null pPendHnyfs

    hnyShiftPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pCurrHnyfs = [f | f@(HierNextYield _) <- S.toList pCurr]
          pPendHnyfs = [f | f@(HierNextYield _) <- S.toList pPend]
      in null pCurrHnyfs && null pPendHnyfs
    --

    -- HBY
    hbyCond clos = not (null [f | f@(HierBackYield _) <- S.toList clos])

    hbyPushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pXl = mustPush (prState info)
          pXr = afterPop (prState info)
          pCurrHbyfs = [f | f@(HierBackYield _) <- S.toList pCurr]
      in if not (null pCurrHbyfs)
           then pXl && pXr
           else True

    hbyShiftPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pCurrHbyfs = [f | f@(HierBackYield _) <- S.toList pCurr]
      in null pCurrHbyfs

    hbyPopFr info =
      let clos = frClos info
          (_, fXl, _, _) = frFuturePendComb info
          fCurr = atomFormulaSet (frFutureCurr info)
          ppCurr = atomFormulaSet . current $ fromJust (frPopped info)
          ppXr = afterPop $ fromJust (frPopped info)
          fCurrHbyfs = [f | f@(HierBackYield _) <- S.toList fCurr]
          checkSet = S.fromList [f | f@(HierBackYield g) <- S.toList clos,
                                                            g `S.member` ppCurr]
      in if fXl
           then if ppXr
                  then S.fromList fCurrHbyfs == checkSet
                  else null fCurrHbyfs
           else True
    --

    -- HNT
    hntCond clos = not (null [f | f@(HierNextTake _) <- S.toList clos])

    hntPopFpr1 info =
      let clos = fprClos info
          (fPend, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)

          fPendHntfs = [f | f@(HierNextTake _) <- S.toList fPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake g) <- S.toList clos,
                                                           hth g `S.member` ppCurr]
      in if not fXl && not fXe
           then S.fromList fPendHntfs == checkSet
           else True

    hntPopFpr2 info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)

          pPendHntfs = [f | f@(HierNextTake _) <- S.toList pPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake _) <- S.toList clos,
                                                           hth f `S.member` ppCurr]
      in if not fXl && not fXe
           then S.fromList pPendHntfs == checkSet
           else True

    hntPopFpr3 info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (_, _, fXe, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake _) <- S.toList clos,
                                                           hth f `S.member` ppCurr]
      in if not (null checkSet)
           then not fXe
           else True

    hntPushFpr1 info =
      let pCurr = atomFormulaSet . current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
          pCurrHntfs = [f | f@(HierNextTake _) <- S.toList pCurr]
      in if not (null pCurrHntfs)
           then fXl
           else True

    hntShiftFpr1 = hntPushFpr1

    hntPushFpr2 info =
      let (fPend, _, _, _) = fprFuturePendComb info
          fPendHntfs = [f | f@(HierNextTake _) <- S.toList fPend]
      in null fPendHntfs

    hntShiftFpr2 = hntPushFpr2
    --

    -- HBT
    hbtCond clos = not (null [f | f@(HierBackTake _) <- S.toList clos])

    hbtPopFpr1 info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)

          pPendHbtfs = [f | f@(HierBackTake _) <- S.toList pPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierBackTake g) <- S.toList clos,
                                                           hth g `S.member` ppCurr]
      in if not fXl && not fXe
           then S.fromList pPendHbtfs == checkSet
           else True

    hbtPopFpr2 info =
      let clos = fprClos info
          (fPend, fXl, _, _) = fprFuturePendComb info
          ppCurr = atomFormulaSet . current $ fromJust (fprPopped info)

          fPendHbtfs = [f | f@(HierBackTake _) <- S.toList fPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierBackTake _) <- S.toList clos,
                                                           hth f `S.member` ppCurr]
      in if not fXl
           then S.fromList fPendHbtfs == checkSet
           else True

    hbtPopFpr3 info =
      let pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          pPendHbtfs = [f | f@(HierBackTake _) <- S.toList pPend]
      in if not (null pPendHbtfs)
           then not fXl && not fXe
           else True

    hbtPushFpr info =
      let pCurr = atomFormulaSet . current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
          pCurrHbtfs = [f | f@(HierBackTake _) <- S.toList pCurr]
      in if not (null pCurrHbtfs)
           then fXl
           else True

    hbtShiftFpr = hbtPushFpr

    hbtPushPr info =
      let pPend = pending (prState info)
          pPendHbtfs = [f | f@(HierBackTake _) <- S.toList pPend]
      in null pPendHbtfs

    hbtShiftPr = hbtPushPr
    --

    -- HTH
    hthCond clos = not (null [f | f@(HierTakeHelper _) <- S.toList clos])

    hthPushPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrHthfs = [f | f@(HierTakeHelper _) <- S.toList pCurr]
          pPendHthfs = [f | f@(HierTakeHelper _) <- S.toList pPend]
      in S.fromList pCurrHthfs == S.fromList pPendHthfs

    hthShiftPr info =
      let pCurr = atomFormulaSet . current $ prState info
          pCurrHthfs = [f | f@(HierTakeHelper _) <- S.toList pCurr]
      in null pCurrHthfs

    hthPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendHthfs = [f | f@(HierTakeHelper _) <- S.toList ppPend]
          fPendHthfs = [f | f@(HierTakeHelper _) <- S.toList fPend]
      in S.fromList ppPendHthfs == S.fromList fPendHthfs

    hthPushFpr info =
      let clos = fprClos info
          pCurr = atomFormulaSet . current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendHthfs = [f | f@(HierTakeHelper _) <- S.toList fPend]
          pCheckSet = S.fromList [f | f@(HierTakeHelper g) <- S.toList clos,
                                                              g `S.member` pCurr]
      in S.fromList fPendHthfs == pCheckSet

    hthShiftFpr = hthPushFpr
    --

data PrInfo a = PrInfo
  { prClos      :: Set (Formula a)
  , prPrecFunc  :: Set (Prop a) -> Set (Prop a) -> Maybe Prec
  , prState     :: State a
  , prProps     :: Maybe (Set (Prop a))
  , prPopped    :: Maybe (State a)
  , prNextProps :: Maybe (Set (Prop a))
  }
data FcrInfo a = FcrInfo
  { fcrClos       :: Set (Formula a)
  , fcrPrecFunc   :: Set (Prop a) -> Set (Prop a) -> Maybe Prec
  , fcrState      :: State a
  , fcrProps      :: Maybe (Set (Prop a))
  , fcrPopped     :: Maybe (State a)
  , fcrFutureCurr :: Atom a
  , fcrNextProps  :: Maybe (Set (Prop a))
  }
data FprInfo a = FprInfo
  { fprClos           :: Set (Formula a)
  , fprPrecFunc       :: Set (Prop a) -> Set (Prop a) -> Maybe Prec
  , fprState          :: State a
  , fprProps          :: Maybe (Set (Prop a))
  , fprPopped         :: Maybe (State a)
  , fprFuturePendComb :: (Set (Formula a), Bool, Bool, Bool)
  , fprNextProps      :: Maybe (Set (Prop a))
  }
data FrInfo a = FrInfo
  { frClos           :: Set (Formula a)
  , frPrecFunc       :: Set (Prop a) -> Set (Prop a) -> Maybe Prec
  , frState          :: State a
  , frProps          :: Maybe (Set (Prop a))
  , frPopped         :: Maybe (State a)
  , frFutureCurr     :: Atom a
  , frFuturePendComb :: (Set (Formula a), Bool, Bool, Bool)
  , frNextProps      :: Maybe (Set (Prop a))
  }

type PresentRule       a = (PrInfo  a -> Bool)
type FutureCurrentRule a = (FcrInfo a -> Bool)
type FuturePendingRule a = (FprInfo a -> Bool)
type FutureRule        a = (FrInfo  a -> Bool)

data RuleGroup a = RuleGroup { ruleGroupPrs  :: [PresentRule       a]
                             , ruleGroupFcrs :: [FutureCurrentRule a]
                             , ruleGroupFprs :: [FuturePendingRule a]
                             , ruleGroupFrs  :: [FutureRule        a]
                             }

augDeltaRules :: (Show a, Ord a) => Set (Formula a) -> (RuleGroup a, RuleGroup a, RuleGroup a)
augDeltaRules cl =
  let (shiftrg, pushrg, poprg) = deltaRules cl
      augShiftRg = shiftrg {ruleGroupFcrs = lookaheadFcr : ruleGroupFcrs shiftrg}
      augPushRg  = pushrg  {ruleGroupFcrs = lookaheadFcr : ruleGroupFcrs pushrg}
      augPopRg   = poprg
  in (augShiftRg, augPushRg, augPopRg)
  where
    lookaheadFcr info = let fCurr = atomFormulaSet (fcrFutureCurr info)
                            nextProps = fromJust (fcrNextProps info)
                        in compProps fCurr nextProps

delta rgroup prec clos atoms pcombs state mprops mpopped mnextprops = fstates
  where
    prs  = ruleGroupPrs  rgroup
    fcrs = ruleGroupFcrs rgroup
    fprs = ruleGroupFprs rgroup
    frs  = ruleGroupFrs  rgroup

    pvalid = null [r | r <- prs, not (r info)]
      where info = PrInfo { prClos      = clos,
                            prPrecFunc  = prec,
                            prState     = state,
                            prProps     = mprops,
                            prPopped    = mpopped,
                            prNextProps = mnextprops
                          }

    vas = filter valid atoms
      where makeInfo curr = FcrInfo { fcrClos       = clos,
                                      fcrPrecFunc   = prec,
                                      fcrState      = state,
                                      fcrProps      = mprops,
                                      fcrPopped     = mpopped,
                                      fcrFutureCurr = curr,
                                      fcrNextProps  = mnextprops
                                    }
            valid atom = null [r | r <- fcrs, not (r $ makeInfo atom)]

    vpcs = S.toList . S.filter valid $ pcombs
      where makeInfo pendComb = FprInfo { fprClos           = clos,
                                          fprPrecFunc       = prec,
                                          fprState          = state,
                                          fprProps          = mprops,
                                          fprPopped         = mpopped,
                                          fprFuturePendComb = pendComb,
                                          fprNextProps      = mnextprops
                                        }
            valid pcomb = null [r | r <- fprs, not (r $ makeInfo pcomb)]

    fstates = if (pvalid)
                then [State curr pend xl xe xr (hashState curr pend xl xe xr) |
                       curr <- vas,
                       pc@(pend, xl, xe, xr) <- vpcs,
                       valid curr pc]
                else []
      where makeInfo curr pendComb = FrInfo { frClos           = clos,
                                              frPrecFunc       = prec,
                                              frState          = state,
                                              frProps          = mprops,
                                              frPopped         = mpopped,
                                              frFutureCurr     = curr,
                                              frFuturePendComb = pendComb,
                                              frNextProps      = mnextprops
                                            }
            valid curr pcomb = null [r | r <- frs, not (r $ makeInfo curr pcomb)]

isFinal :: (Eq a, Show a) => State a -> Bool
isFinal s@(State c p xl xe xr _) = debug $ not xl && -- xe can be instead accepted, as if # = #
                                           currAtomic == S.singleton (Atomic End) &&
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

check :: (Checkable f, Ord a, Hashable a, Show a)
      => f a
      -> (Set (Prop a) -> Set (Prop a) -> Maybe Prec)
      -> [Set (Prop a)]
      -> Bool
check phi prec ts =
  debug $ run
            prec
            is
            isFinal
            (deltaShift cl as pcs prec shiftRules)
            (deltaPush  cl as pcs prec  pushRules)
            (deltaPop   cl as pcs prec   popRules)
            ts
  where nphi = normalize . toReducedPotl $ phi
        tsprops = S.toList $ foldl' (S.union) S.empty ts
        inputSet = foldl' (flip S.insert) S.empty ts
        cl = closure nphi tsprops
        as = atoms cl inputSet
        pcs = pendCombs cl
        is = initials nphi cl as
        (shiftRules, pushRules, popRules) = deltaRules cl
        debug = id

        deltaShift clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop clos atoms pcombs prec rgroup state popped = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                Nothing (Just popped) Nothing

fastcheck :: (Checkable f, Ord a, Hashable a, Show a)
          => f a
          -> (Set (Prop a) -> Set (Prop a) -> Maybe Prec)
          -> [Set (Prop a)]
          -> Bool
fastcheck phi prec ts =
  debug $ augRun
            prec
            is
            isFinal
            (augDeltaShift cl as pcs prec shiftRules)
            (augDeltaPush  cl as pcs prec  pushRules)
            (augDeltaPop   cl as pcs prec   popRules)
            ts
  where nphi = normalize . toReducedPotl $ phi

        tsprops = S.toList $ foldl' (S.union) S.empty ts
        inputSet = foldl' (flip S.insert) S.empty ts

        cl = closure nphi tsprops
        as = atoms cl inputSet
        pcs = pendCombs cl
        is = filter compInitial (initials nphi cl as)
        (shiftRules, pushRules, popRules) = augDeltaRules cl

        compInitial s = fromMaybe True $
                          compProps <$> (Just . atomFormulaSet . current) s <*> safeHead ts

        debug = id
        --debug = DT.trace ("\nRun with:"         ++
        --                  "\nNorm. phi:    "    ++ show nphi         ++
        --                  "\nTokens:       "    ++ show ts           ++
        --                  "\nToken props:\n"    ++ show tsprops      ++
        --                  "\nClosure:\n"        ++ showFormulaSet cl ++
        --                  "\nAtoms:\n"          ++ showAtoms as      ++
        --                  "\nPending atoms:\n"  ++ showPendCombs pcs ++
        --                  "\nInitial states:\n" ++ showStates is)

        laProps lookahead = case lookahead of
                                     Just npset -> npset
                                     Nothing    -> S.singleton End

        augDeltaShift clos atoms pcombs prec rgroup lookahead state props = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nShift with: " ++ show (S.toList props) ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup prec clos atoms pcombs state
                            (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPush clos atoms pcombs prec rgroup lookahead state props = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nPush with: " ++ show (S.toList props) ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup prec clos atoms pcombs state
                            (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPop clos atoms pcombs prec rgroup lookahead state popped = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nPop with popped:\n" ++ show popped ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup prec clos atoms pcombs state
                            Nothing (Just popped) (Just . laProps $ lookahead)

makeOpa :: (Checkable f, Ord a, Hashable a, Show a)
        => f a
        -> ([Prop a], [Prop a])
        -> (Set (Prop a) -> Set (Prop a) -> Maybe Prec)
        -> ([State a],
            State a -> Bool,
            State a -> Set (Prop a) -> [State a],
            State a -> Set (Prop a) -> [State a],
            State a -> State a -> [State a])
makeOpa phi (sls, als) prec = (is, isFinal,
                          deltaPush  cl as pcs prec pushRules,
                          deltaShift cl as pcs prec shiftRules,
                          deltaPop   cl as pcs prec popRules)
  where nphi = normalize . toReducedPotl $ phi
        tsprops = sls ++ als
        inputSet = S.fromList [S.fromList (sl:alt) | sl <- sls, alt <- filterM (const [True, False]) als]
        cl = closure nphi tsprops
        as = atoms cl inputSet
        pcs = pendCombs cl
        is = initials nphi cl as
        (shiftRules, pushRules, popRules) = deltaRules cl

        deltaShift clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop clos atoms pcombs prec rgroup state popped = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                Nothing (Just popped) Nothing
