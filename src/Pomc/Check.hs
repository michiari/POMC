{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Check
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Check ( -- * Checking functions
                    check
                  , checkGen
                  , fastcheck
                  , fastcheckGen
                    -- * Checking typeclass
                  , Checkable(..)
                    -- * Checking helpers
                  , closure
                    -- * Printing
                  , showAtoms
                  , showStates
                  , Input(..)
                  , Atom(..)
                  , State(..)
                  , getProps
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), PrecFunc, StructPrecRel, fromStructPR)
import Pomc.Opa (run, augRun)
import Pomc.RPotl (Formula(..), negative, atomic, normalize, future)
import Pomc.Util (xor, implies, safeHead)
import Pomc.Data (FormulaSet, EncodedSet, BitEncoding(..))
import qualified Pomc.Data as D
import Pomc.PropConv (APType, convPropTokens)

import Data.Maybe (fromJust, fromMaybe, isNothing)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector (Vector)
import qualified Data.Vector as V

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

-- Input symbol
type Input = Set (Prop APType)

type Atom = EncodedSet

data State = State
    { current   :: Atom
    , pending   :: Set (Formula APType)
    , mustPush  :: !Bool
    , mustShift :: !Bool
    , afterPop  :: !Bool
    } deriving (Generic, NFData, Ord, Eq)

instance Hashable State

showFormulaSet :: FormulaSet -> String
showFormulaSet fset = let fs = S.toList fset
                          posfs = filter (not . negative) fs
                          negfs = filter (negative) fs
                      in show (posfs ++ negfs)

showAtom :: BitEncoding -> Atom -> String
showAtom bitenc atom = "FS: " ++ showFormulaSet (D.decode bitenc atom) ++ "\t\tES: " ++ show atom

instance Show State where
  show (State c p xl xe xr) = "\n{ C: "  ++ show c             ++
                              "\n, P: "  ++ show (S.toList p)  ++
                              "\n, XL: " ++ show xl            ++
                              "\n, X=: " ++ show xe            ++
                              "\n, XR: " ++ show xr            ++
                              "\n}"

showState :: BitEncoding -> State -> String
showState bitenc (State c p xl xe xr) =
  "\n{ C: "  ++ showAtom bitenc c  ++
  "\n, P: "  ++ show (S.toList p)  ++
  "\n, XL: " ++ show xl            ++
  "\n, X=: " ++ show xe            ++
  "\n, XR: " ++ show xr            ++
  "\n}"

showAtoms :: BitEncoding -> [Atom] -> String
showAtoms bitenc = unlines . map (showAtom bitenc)

showPendCombs :: Set (FormulaSet, Bool, Bool, Bool) -> String
showPendCombs = unlines . map show . S.toList

showStates :: [State] -> String
showStates = unlines . map show

atomicSet :: BitEncoding -> EncodedSet -> EncodedSet
atomicSet bitenc set = D.filter bitenc atomic set

compProps :: BitEncoding -> EncodedSet -> Input -> Bool
compProps bitenc fset pset = atomicSet bitenc fset == D.encode bitenc (S.map Atomic pset)

getProps :: BitEncoding -> EncodedSet -> Input
getProps bitenc fset = S.map (\(Atomic p) -> p) $ D.pdecode bitenc $ D.propsOnly bitenc fset

closure :: Formula APType -> [Prop APType] -> FormulaSet
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

atoms :: FormulaSet -> Set (Input) -> ([Atom], BitEncoding)
atoms clos inputSet =
  let validPropSets = S.insert (S.singleton End) inputSet

      pclos = S.filter (not . negative) clos

      fetch vec i = vec V.! i

      -- Mapping between positive formulas and bits
      pFormulaClos = S.filter (not . atomic) pclos
      pFormulaVec = V.fromList . S.toAscList $ pFormulaClos
      pFormulaMap = M.fromAscList (zip (S.toAscList pFormulaClos) [0..])
      pFormulaLookup phi = fromJust (M.lookup phi pFormulaMap)
      fbitenc = BitEncoding (fetch pFormulaVec) pFormulaLookup (V.length pFormulaVec) 0

      -- Mapping between positive atoms and bits
      pAtomicClos = S.filter (atomic) pclos
      pAtomicVec = V.fromList . S.toAscList $ pAtomicClos
      pAtomicMap = M.fromAscList (zip (S.toAscList pAtomicClos) [0..])
      pAtomicLookup phi = fromJust (M.lookup phi pAtomicMap)
      abitenc = BitEncoding
                (fetch pAtomicVec)
                pAtomicLookup
                (V.length pAtomicVec)
                (V.length pAtomicVec)

      -- Mapping between positive closure and bits
      pClosVec = pAtomicVec V.++ pFormulaVec
      pClosLookup phi = fromJust $ M.lookup phi pClosMap
        where pClosMap = pAtomicMap `M.union` M.map (V.length pAtomicVec +) pFormulaMap
      bitenc = BitEncoding (fetch pClosVec) pClosLookup (V.length pClosVec) (V.length pAtomicVec)

      -- Make power set of AP
      atomics = map (D.encode abitenc) . map (S.map Atomic) $ S.toList validPropSets

      -- Consistency checks
      checks =
        [ onlyif (T `S.member` clos) (trueCons bitenc)
        , onlyif (not . null $ [f | f@(And _ _)            <- cl]) (andCons bitenc clos)
        , onlyif (not . null $ [f | f@(Or _ _)             <- cl]) (orCons bitenc clos)
        , onlyif (not . null $ [f | f@(ChainNext _ _)      <- cl]) (chainNextCons bitenc clos)
        , onlyif (not . null $ [f | f@(ChainBack _ _)      <- cl]) (chainBackCons bitenc clos)
        , onlyif (not . null $ [f | f@(Until _ _ _)        <- cl]) (untilCons bitenc clos)
        , onlyif (not . null $ [f | f@(Since _ _ _)        <- cl]) (sinceCons bitenc clos)
        , onlyif (not . null $ [f | f@(HierUntilYield _ _) <- cl]) (hierUntilYieldCons bitenc clos)
        , onlyif (not . null $ [f | f@(HierSinceYield _ _) <- cl]) (hierSinceYieldCons bitenc clos)
        , onlyif (not . null $ [f | f@(HierUntilTake _ _)  <- cl]) (hierUntilTakeCons bitenc clos)
        , onlyif (not . null $ [f | f@(HierSinceTake _ _)  <- cl]) (hierSinceTakeCons bitenc clos)
        , onlyif (not . null $ [f | f@(Eventually' _)      <- cl]) (evCons bitenc clos)
        ]
        where onlyif cond f = if cond then f else const True
              cl = S.toList clos
      consistent eset = all (\c -> c eset) checks

      -- Make all consistent atoms
      prependCons as eset =
        let combs = do easet <- atomics
                       let eset' = easet D.++ eset
                       guard (consistent eset')
                       return eset'
        in as SQ.>< (SQ.fromList combs)

      combineAtoms 0 = SQ.fromList atomics
      combineAtoms len = foldl' prependCons SQ.empty (D.generate len)

  in (toList $ combineAtoms (V.length pFormulaVec), bitenc)

trueCons :: BitEncoding -> EncodedSet -> Bool
trueCons bitenc set = not $ D.member bitenc (Not T) set

andCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
andCons bitenc clos set = not (D.any bitenc consSet set)
                          &&
                          null [f | f@(And g h) <- S.toList clos,
                                 (D.member bitenc g set) &&
                                 (D.member bitenc h set) &&
                                 not (D.member bitenc f set)]
  where consSet (And g h) = not $ D.member bitenc g set && D.member bitenc h set
        consSet _ = False

orCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
orCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         null [f | f@(Or g h) <- S.toList clos,
                                ((D.member bitenc g set) ||
                                 (D.member bitenc h set)
                                ) && not (D.member bitenc f set)]
  where consSet (Or g h) = not $ D.member bitenc g set || D.member bitenc h set
        consSet _ = False

chainNextCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
chainNextCons bitenc clos set = not (D.any bitenc consSet set)
                                &&
                                null [f | f@(ChainNext pset g) <- S.toList clos,
                                                                  S.size pset > 1 &&
                                                                  present pset g &&
                                                                  not (D.member bitenc f set)]
  where present pset g = any (\p -> D.member bitenc (ChainNext (S.singleton p) g) set)
                             (S.toList pset)
        consSet (ChainNext pset g) = S.size pset > 1 && not (present pset g)
        consSet _ = False

chainBackCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
chainBackCons bitenc clos set = not (D.any bitenc consSet set)
                                &&
                                null [f | f@(ChainBack pset g) <- S.toList clos,
                                                                  S.size pset > 1 &&
                                                                  present pset g &&
                                                                  not (D.member bitenc f set)]
  where present pset g = any (\p -> D.member bitenc (ChainBack (S.singleton p) g) set)
                             (S.toList pset)
        consSet (ChainBack pset g) = S.size pset > 1 && not (present pset g)
        consSet _ = False

untilCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
untilCons bitenc clos set = not (D.any bitenc consSet set)
                            &&
                            null [f | f@(Until pset g h) <- S.toList clos,
                                                            present f pset g h &&
                                                            not (D.member bitenc f set)]
  where present u pset g h = D.member bitenc h set
                             || (D.member bitenc g set
                                 && (D.member bitenc (PrecNext  pset u) set
                                     || D.member bitenc (ChainNext pset u) set))
        consSet f@(Until pset g h) = not $ present f pset g h
        consSet _ = False

sinceCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
sinceCons bitenc clos set = not (D.any bitenc consSet set)
                            &&
                            null [f | f@(Since pset g h) <- S.toList clos,
                                                            present f pset g h &&
                                                            not (D.member bitenc f set)]
  where present s pset g h = D.member bitenc h set
                             || (D.member bitenc g set
                                 && (D.member bitenc (PrecBack pset s) set
                                     || D.member bitenc (ChainBack pset s) set))
        consSet f@(Since pset g h) = not $ present f pset g h
        consSet _ = False

hierUntilYieldCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierUntilYieldCons bitenc clos set = not (D.any bitenc consSet set)
                                     &&
                                     null [f | f@(HierUntilYield g h) <- S.toList clos,
                                                                         present f g h &&
                                                                         not (D.member bitenc f set)]
  where present huy g h =
          (D.member bitenc h set && D.member bitenc (ChainBack (S.singleton Yield) T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HierNextYield huy) set)
        consSet f@(HierUntilYield g h) = not $ present f g h
        consSet _ = False

hierSinceYieldCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierSinceYieldCons bitenc clos set = not (D.any bitenc consSet set)
                                     &&
                                     null [f | f@(HierSinceYield g h) <- S.toList clos,
                                                                         present f g h &&
                                                                         not (D.member bitenc f set)]
  where present hsy g h =
          (D.member bitenc h set && D.member bitenc (ChainBack (S.singleton Yield) T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HierBackYield hsy) set)
        consSet f@(HierSinceYield g h) = not $ present f g h
        consSet _ = False

hierUntilTakeCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierUntilTakeCons bitenc clos set = not (D.any bitenc consSet set)
                                    &&
                                    null [f | f@(HierUntilTake g h) <- S.toList clos,
                                                                       present f g h &&
                                                                       not (D.member bitenc f set)]
  where present hut g h =
          (D.member bitenc h set && D.member bitenc (ChainNext (S.singleton Take) T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HierNextTake hut) set)
        consSet f@(HierUntilTake g h) = not $ present f g h
        consSet _ = False

hierSinceTakeCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierSinceTakeCons bitenc clos set = not (D.any bitenc consSet set)
                                    &&
                                    null [f | f@(HierSinceTake g h) <- S.toList clos,
                                                                       present f g h &&
                                                                       not (D.member bitenc f set)]
  where present hst g h =
          (D.member bitenc h set && D.member bitenc (ChainNext (S.singleton Take) T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HierBackTake hst) set)
        consSet f@(HierSinceTake g h) = not $ present f g h
        consSet _ = False

evCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
evCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         null [f | f@(Eventually' g) <- S.toList clos,
                                                        present f g &&
                                                        not (D.member bitenc f set)]
  where present ev g =
          (D.member bitenc g set) ||
          (D.member bitenc (PrecNext (S.fromList [Yield, Equal, Take]) ev) set)
        consSet f@(Eventually' g) = not $ present f g
        consSet _ = False

pendCombs :: FormulaSet -> Set (FormulaSet, Bool, Bool, Bool)
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

initials :: Formula APType -> FormulaSet -> ([Atom], BitEncoding) -> [State]
initials phi clos (atoms, bitenc) =
  let compatible atom = let set = atom
                            checkPb (PrecBack {}) = True
                            checkPb _ = False
                        in D.member bitenc phi set &&
                           (not $ D.any bitenc checkPb set)
      compAtoms = filter compatible atoms
      cnyfSet = S.fromList [f | f@(ChainNext pset _) <- S.toList clos,
                                                        pset == (S.singleton Yield)]
  in [State ia ip True False False | ia <- compAtoms,
                                     ip <- S.toList (S.powerSet cnyfSet)]

resolve :: i -> [(i -> Bool, b)] -> [b]
resolve info conditionals = snd . unzip $ filter (\(cond, _) -> cond info) conditionals

deltaRules :: BitEncoding -> FormulaSet -> (RuleGroup, RuleGroup, RuleGroup)
deltaRules bitenc condInfo =
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
        , ruleGroupFcrs = resolve condInfo []
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
      let pCurr = current $ prState info
          props = fromJust (prProps info)
      in compProps bitenc pCurr props

    propShiftPr = propPushPr
    --

    -- PN rules
    pnCond clos = not (null [f | f@(PrecNext _ _) <- S.toList clos])

    pnPushFcr info =
      let clos = fcrClos info
          pCurr = current $ fcrState info
          precFunc = fcrPrecFunc info
          props = fromJust (fcrProps info)
          fCurr = fcrFutureCurr info

          maskPn = D.suchThat bitenc checkPn
          checkPn (PrecNext _ _) = True
          checkPn _ = False

          pCurrPnfs = D.intersect pCurr maskPn
          precComp prec = not $ D.any bitenc (\(PrecNext pset _) -> prec `S.notMember` pset) pCurrPnfs

          fsComp prec = pCurrPnfs == checkSet
            where checkSet = D.encode bitenc $ S.filter checkSetPred closPn
                  checkSetPred (PrecNext pset g) = prec `S.member` pset && D.member bitenc g fCurr
                  checkSetPred _ = False
          closPn = S.filter checkPn clos

      in case precFunc props (getProps bitenc fCurr) of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pnShiftFcr = pnPushFcr
    --

    -- PB rules
    pbCond clos = not (null [f | f@(PrecBack _ _) <- S.toList clos])

    pbPushFcr info =
      let clos = fcrClos info
          pCurr = current $ fcrState info
          precFunc = fcrPrecFunc info
          props = fromJust (fcrProps info)
          fCurr = fcrFutureCurr info

          maskPb = D.suchThat bitenc checkPb
          checkPb (PrecBack _ _) = True
          checkPb _ = False

          fCurrPbfs = D.intersect fCurr maskPb

          precComp prec = not $ D.any bitenc (\(PrecBack pset _) -> prec `S.notMember` pset) fCurrPbfs

          fsComp prec = fCurrPbfs == checkSet
            where checkSet = D.encode bitenc $ S.filter checkSetPred closPb
                  checkSetPred (PrecBack pset g) = prec `S.member` pset && D.member bitenc g pCurr
                  checkSetPred _ = False
          closPb = S.filter checkPb clos

      in case precFunc props (getProps bitenc fCurr) of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pbShiftFcr = pbPushFcr
    --

    -- CNY
    maskCny = D.suchThat bitenc checkCny
    checkCny (ChainNext _ _) = True
    checkCny _ = False

    cnyCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == S.singleton Yield])

    cnyPushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          pCurrCnyfs = D.filter bitenc checkCnyY $ D.intersect pCurr maskCny
          fPendCnyfs = D.encode bitenc $ S.filter checkCnyY fPend

          checkCnyY (ChainNext pset _) = pset == S.singleton Yield
          checkCnyY _ = False
      in if fXl
           then pCurrCnyfs == fPendCnyfs
           else D.null pCurrCnyfs

    cnyShiftFpr = cnyPushFpr

    cnyPopFpr info =
      let clos = fprClos info
          pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          ppPend = pending $ fromJust (fprPopped info)
          ppPendCnyfs = [f | f@(ChainNext pset _) <- S.toList ppPend,
                                                     pset == S.singleton Yield]
          pCheckSet = S.fromList [f | f@(ChainNext pset g) <- S.toList clos,
                                                              pset == S.singleton Yield &&
                                                              D.member bitenc g pCurr]
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
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCnefs = D.encode bitenc $ S.filter checkCne fPend
          pCurrCnefs = D.filter bitenc checkCne pCurr
          checkCne (ChainNext pset _) = pset == S.singleton Equal
          checkCne _ = False
      in if fXl
           then pCurrCnefs == fPendCnefs
           else D.null pCurrCnefs

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
          pCurr = current $ prState info
          pPend = pending (prState info)
          pPendCnefs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Equal]
          pCheckList = [f | f@(ChainNext pset g) <- S.toList clos,
                                                    pset == S.singleton Equal,
                                                    D.member bitenc g pCurr]
      in S.fromList pCheckList == S.fromList pPendCnefs
    --

    -- CNT rules
    cntCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == S.singleton Take])

    cntPushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCntfs = D.encode bitenc $ S.filter checkCnt fPend
          pCurrCntfs = D.filter bitenc checkCnt pCurr
          checkCnt (ChainNext pset _) = pset == S.singleton Take
          checkCnt _ = False
      in if fXl
           then pCurrCntfs == fPendCntfs
           else D.null pCurrCntfs

    cntShiftFpr = cntPushFpr

    cntPopPr info =
      let clos = prClos info
          pCurr = current $ prState info
          pPend = pending (prState info)
          pPendCntfs = [f | f@(ChainNext pset _) <- S.toList pPend,
                                                    pset == S.singleton Take]
          pCheckList = [f | f@(ChainNext pset g) <- S.toList clos,
                                                    pset == S.singleton Take,
                                                    D.member bitenc g pCurr]
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
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbyfs = D.filter bitenc checkCby pCurr
          pPendCbyfs = D.encode bitenc $ S.filter checkCby pPend
          checkCby (ChainBack pset _) = pset == S.singleton Yield
          checkCby _ = False
      in if pXr
           then pCurrCbyfs == pPendCbyfs
           else D.null pCurrCbyfs

    cbyShiftPr info =
      let pCurr = current $ prState info
          checkCby (ChainBack pset _) = pset == S.singleton Yield
          checkCby _ = False
      in not $ D.any bitenc checkCby pCurr

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
          pCurr = current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendCbyfs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Yield]
          pCheckSet = S.fromList [f | f@(ChainBack pset g) <- S.toList clos,
                                                              pset == S.singleton Yield &&
                                                              D.member bitenc g pCurr]
      in S.fromList fPendCbyfs == pCheckSet

    cbyShiftFpr = cbyPushFpr
    --

    -- CBE
    cbeCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == S.singleton Equal])

    cbeShiftPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbefs = D.filter bitenc checkCbe pCurr
          pPendCbefs = D.encode bitenc $ S.filter checkCbe pPend
          checkCbe (ChainBack pset _) = pset == S.singleton Equal
          checkCbe _ = False
      in if pXr
           then pCurrCbefs == pPendCbefs
           else D.null pCurrCbefs

    cbePushPr info =
      let pCurr = current $ prState info
          checkCbe (ChainBack pset _) = pset == S.singleton Equal
          checkCbe _ = False
      in not $ D.any bitenc checkCbe pCurr

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
          pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info

          fPendCbefs = [f | f@(ChainBack pset _) <- S.toList fPend,
                                                    pset == S.singleton Equal]
          pCheckSet = S.fromList [f | f@(ChainBack pset g) <- S.toList clos,
                                                              pset == S.singleton Equal &&
                                                              D.member bitenc g pCurr]
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
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbtfs = D.filter bitenc checkCbt pCurr
          pPendCbtfs = D.encode bitenc $ S.filter checkCbt pPend
          checkCbt (ChainBack pset _) = pset == S.singleton Take
          checkCbt _ = False
      in if pXr
           then pCurrCbtfs == pPendCbtfs
           else D.null pCurrCbtfs

    cbtShiftPr = cbtPushPr

    cbtPopFpr info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (fPend, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = (D.decode bitenc) . current $ fromJust (fprPopped info)
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
    maskHny = D.suchThat bitenc checkHny
    checkHny (HierNextYield _) = True
    checkHny _ = False

    hnyCond clos = not (null [f | f@(HierNextYield _) <- S.toList clos])

    hnyPushPr1 info =
      let pCurr = current $ prState info
          pXr = afterPop (prState info)
      in if not $ D.null $ D.intersect pCurr maskHny
           then pXr
           else True

    hnyPushPr2 info =
      let clos = prClos info
          pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pPendHnyfs = [f | f@(HierNextYield _) <- S.toList pPend]
          checkSet = S.fromList [f | f@(HierNextYield g) <- S.toList clos,
                                                            D.member bitenc g pCurr]
      in if pXr
           then checkSet == S.fromList pPendHnyfs
           else null pPendHnyfs

    hnyPopFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)
          ppXr = afterPop $ fromJust (fprPopped info)
          fPendHnyfs = D.encode bitenc $ S.filter checkHny fPend
          ppCurrHnyfs = D.intersect maskHny ppCurr
      in if ppXr
           then ppCurrHnyfs == fPendHnyfs
           else True

    hnyPopPr info =
      let pPend = pending (prState info)
          pPendHnyfs = [f | f@(HierNextYield _) <- S.toList pPend]
      in null pPendHnyfs

    hnyShiftPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pPendHnyfs = S.filter checkHny pPend
          checkHny (HierNextYield _) = True
          checkHny _ = False
      in (not $ D.any bitenc checkHny pCurr) && S.null pPendHnyfs
    --

    -- HBY
    checkHby (HierBackYield _) = True
    checkHby _ = False

    hbyCond clos = not (null [f | f@(HierBackYield _) <- S.toList clos])

    hbyPushPr info =
      let pCurr = current $ prState info
          pXl = mustPush (prState info)
          pXr = afterPop (prState info)
      in if D.any bitenc checkHby pCurr
           then pXl && pXr
           else True

    hbyShiftPr info =
      let pCurr = current $ prState info
      in not $ D.any bitenc checkHby pCurr

    hbyPopFr info =
      let clos = frClos info
          (_, fXl, _, _) = frFuturePendComb info
          fCurr = (D.decode bitenc) $ frFutureCurr info
          ppCurr = current $ fromJust (frPopped info)
          ppXr = afterPop $ fromJust (frPopped info)
          fCurrHbyfs = [f | f@(HierBackYield _) <- S.toList fCurr]
          checkSet = S.fromList [f | f@(HierBackYield g) <- S.toList clos,
                                                            D.member bitenc g ppCurr]
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
          ppCurr = current $ fromJust (fprPopped info)

          fPendHntfs = [f | f@(HierNextTake _) <- S.toList fPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake g) <- S.toList clos,
                                                           D.member bitenc (hth g) ppCurr]
      in if not fXl && not fXe
           then S.fromList fPendHntfs == checkSet
           else True

    hntPopFpr2 info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          pPendHntfs = [f | f@(HierNextTake _) <- S.toList pPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake _) <- S.toList clos,
                                                           D.member bitenc (hth f) ppCurr]
      in if not fXl && not fXe
           then S.fromList pPendHntfs == checkSet
           else True

    hntPopFpr3 info =
      let clos = fprClos info
          pPend = pending (fprState info)
          (_, _, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierNextTake _) <- S.toList clos,
                                                           D.member bitenc (hth f) ppCurr]
      in if not (null checkSet)
           then not fXe
           else True

    hntPushFpr1 info =
      let pCurr = current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
          checkHnt (HierNextTake _) = True
          checkHnt _ = False
      in if D.any bitenc checkHnt pCurr
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
          ppCurr = current $ fromJust (fprPopped info)

          pPendHbtfs = [f | f@(HierBackTake _) <- S.toList pPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierBackTake g) <- S.toList clos,
                                                           D.member bitenc (hth g) ppCurr]
      in if not fXl && not fXe
           then S.fromList pPendHbtfs == checkSet
           else True

    hbtPopFpr2 info =
      let clos = fprClos info
          (fPend, fXl, _, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          fPendHbtfs = [f | f@(HierBackTake _) <- S.toList fPend]

          hth = HierTakeHelper
          checkSet = S.fromList [f | f@(HierBackTake _) <- S.toList clos,
                                                           D.member bitenc (hth f) ppCurr]
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
      let pCurr = current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
          checkHbt (HierBackTake _) = True
          checkHbt _ = False
      in if D.any bitenc checkHbt pCurr
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
    checkHth (HierTakeHelper _) = True
    checkHth _ = False

    hthCond clos = not (null [f | f@(HierTakeHelper _) <- S.toList clos])

    hthPushPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrHthfs = D.filter bitenc checkHth pCurr
          pPendHthfs = D.encode bitenc $ S.filter checkHth pPend
      in pCurrHthfs == pPendHthfs

    hthShiftPr info =
      let pCurr = current $ prState info
      in not $ D.any bitenc checkHth pCurr

    hthPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendHthfs = [f | f@(HierTakeHelper _) <- S.toList ppPend]
          fPendHthfs = [f | f@(HierTakeHelper _) <- S.toList fPend]
      in S.fromList ppPendHthfs == S.fromList fPendHthfs

    hthPushFpr info =
      let clos = fprClos info
          pCurr = current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendHthfs = [f | f@(HierTakeHelper _) <- S.toList fPend]
          pCheckSet = S.fromList [f | f@(HierTakeHelper g) <- S.toList clos,
                                                              D.member bitenc g pCurr]
      in S.fromList fPendHthfs == pCheckSet

    hthShiftFpr = hthPushFpr
    --

data PrInfo = PrInfo
  { prClos      :: FormulaSet
  , prPrecFunc  :: PrecFunc APType
  , prState     :: State
  , prProps     :: Maybe (Input)
  , prPopped    :: Maybe (State)
  , prNextProps :: Maybe (Input)
  }
data FcrInfo = FcrInfo
  { fcrClos       :: FormulaSet
  , fcrPrecFunc   :: PrecFunc APType
  , fcrState      :: State
  , fcrProps      :: Maybe (Input)
  , fcrPopped     :: Maybe (State)
  , fcrFutureCurr :: Atom
  , fcrNextProps  :: Maybe (Input)
  }
data FprInfo = FprInfo
  { fprClos           :: FormulaSet
  , fprPrecFunc       :: PrecFunc APType
  , fprState          :: State
  , fprProps          :: Maybe (Input)
  , fprPopped         :: Maybe (State)
  , fprFuturePendComb :: (FormulaSet, Bool, Bool, Bool)
  , fprNextProps      :: Maybe (Input)
  }
data FrInfo = FrInfo
  { frClos           :: FormulaSet
  , frPrecFunc       :: PrecFunc APType
  , frState          :: State
  , frProps          :: Maybe (Input)
  , frPopped         :: Maybe (State)
  , frFutureCurr     :: Atom
  , frFuturePendComb :: (FormulaSet, Bool, Bool, Bool)
  , frNextProps      :: Maybe (Input)
  }

type PresentRule       = (PrInfo  -> Bool)
type FutureCurrentRule = (FcrInfo -> Bool)
type FuturePendingRule = (FprInfo -> Bool)
type FutureRule        = (FrInfo  -> Bool)

data RuleGroup = RuleGroup { ruleGroupPrs  :: [PresentRule      ]
                           , ruleGroupFcrs :: [FutureCurrentRule]
                           , ruleGroupFprs :: [FuturePendingRule]
                           , ruleGroupFrs  :: [FutureRule       ]
                           }

augDeltaRules :: BitEncoding -> FormulaSet -> (RuleGroup, RuleGroup, RuleGroup)
augDeltaRules bitenc cl =
  let (shiftrg, pushrg, poprg) = deltaRules bitenc cl
      augShiftRg = shiftrg {ruleGroupFcrs = lookaheadFcr : ruleGroupFcrs shiftrg}
      augPushRg  = pushrg  {ruleGroupFcrs = lookaheadFcr : ruleGroupFcrs pushrg}
      augPopRg   = poprg
  in (augShiftRg, augPushRg, augPopRg)
  where
    lookaheadFcr info = let fCurr = fcrFutureCurr info
                            nextProps = fromJust (fcrNextProps info)
                        in compProps bitenc fCurr nextProps

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

    vas = filter valid nextAtoms
      where makeInfo curr = FcrInfo { fcrClos       = clos,
                                      fcrPrecFunc   = prec,
                                      fcrState      = state,
                                      fcrProps      = mprops,
                                      fcrPopped     = mpopped,
                                      fcrFutureCurr = curr,
                                      fcrNextProps  = mnextprops
                                    }
            valid atom = null [r | r <- fcrs, not (r $ makeInfo atom)]
            nextAtoms = if isNothing mpopped
                        then atoms
                        else [current state]

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
                then [State curr pend xl xe xr | curr <- vas,
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

isFinal :: BitEncoding -> State -> Bool
isFinal bitenc s@(State c p xl xe xr) =
  debug $ not xl -- xe can be instead accepted, as if # = #
  && D.member bitenc (Atomic End) currFset
  && (not $ D.any bitenc future currFset)
  && pendComb
  where currFset = current s
        currAtomic = D.filter bitenc atomic currFset
        pendComb = all (\f -> case f of  -- only ChainBack Take formulas are allowed
                                ChainBack pset _ -> pset == S.singleton Take
                                _ -> False
                       ) (S.toList $ pending s)
        debug = id
        --debug = DT.trace ("\nIs state final?" ++ show s) . DT.traceShowId

check :: Formula APType
      -> PrecFunc APType
      -> [Set (Prop APType)]
      -> Bool
check phi prec ts =
  debug $ run
            prec
            is
            (isFinal bitenc)
            (deltaShift cl as pcs prec shiftRules)
            (deltaPush  cl as pcs prec  pushRules)
            (deltaPop   cl as pcs prec   popRules)
            ts
  where nphi = normalize . toReducedPotl $ phi
        tsprops = S.toList $ foldl' (S.union) S.empty ts
        inputSet = foldl' (flip S.insert) S.empty ts
        cl = closure nphi tsprops
        ab@(as, bitenc) = atoms cl inputSet
        pcs = pendCombs cl
        is = initials nphi cl ab
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl
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

checkGen :: (Checkable f, Ord a, Show a)
         => f a
         -> [StructPrecRel a]
         -> [Set (Prop a)]
         -> Bool
checkGen phi precr ts =
  let (tphi, tprecr, tts) = convPropTokens (toReducedPotl phi) precr ts
  in check tphi (fromStructPR tprecr) tts


fastcheck :: Formula APType
          -> PrecFunc APType
          -> [Set (Prop APType)]
          -> Bool
fastcheck phi prec ts =
  debug $ augRun
            prec
            is
            (isFinal bitenc)
            (augDeltaShift cl as pcs prec shiftRules)
            (augDeltaPush  cl as pcs prec  pushRules)
            (augDeltaPop   cl as pcs prec   popRules)
            ts
  where nphi = normalize . toReducedPotl $ phi

        tsprops = S.toList $ foldl' (S.union) S.empty ts
        inputSet = foldl' (flip S.insert) S.empty ts

        cl = closure nphi tsprops
        ab@(as, bitenc) = atoms cl inputSet
        pcs = pendCombs cl
        is = filter compInitial (initials nphi cl ab)
        (shiftRules, pushRules, popRules) = augDeltaRules bitenc cl

        compInitial s = fromMaybe True $
                          (compProps bitenc) <$> (Just . current) s <*> safeHead ts

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

fastcheckGen :: (Checkable f, Ord a, Show a)
             => f a
             -> [StructPrecRel a]
             -> [Set (Prop a)]
             -> Bool
fastcheckGen phi precr ts =
  let (tphi, tprecr, tts) = convPropTokens (toReducedPotl phi) precr ts
  in fastcheck tphi (fromStructPR tprecr) tts


makeOpa :: (Checkable f)
        => f APType
        -> ([Prop APType], [Prop APType])
        -> PrecFunc APType
        -> (BitEncoding
           , [State]
           , State -> Bool
           , State -> Input -> [State]
           , State -> Input -> [State]
           , State -> State -> [State]
           )
makeOpa phi (sls, als) prec = (bitenc
                              , is
                              , isFinal bitenc
                              , deltaPush  cl as pcs prec pushRules
                              ,  deltaShift cl as pcs prec shiftRules
                              ,  deltaPop   cl as pcs prec popRules
                              )
  where nphi = normalize . toReducedPotl $ phi
        tsprops = sls ++ als
        inputSet = S.fromList [S.fromList (sl:alt) | sl <- sls, alt <- filterM (const [True, False]) als]
        cl = closure nphi tsprops
        ab@(as, bitenc) = atoms cl inputSet
        pcs = pendCombs cl
        is = initials nphi cl ab
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl

        deltaShift clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop clos atoms pcombs prec rgroup state popped = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                Nothing (Just popped) Nothing
