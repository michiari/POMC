{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Check
   Copyright   : 2020 Davide Bergamaschi and Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
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
                  , EncPrecFunc
                  , Input(..)
                  , Atom(..)
                  , State(..)
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import qualified Pomc.Prec as PS (singleton, size, member, notMember, fromList, toList)
import Pomc.Opa (run, augRun)
import Pomc.RPotl (Formula(..), negative, atomic, normalize, future)
import Pomc.Util (xor, implies, safeHead)
import Pomc.Data (EncodedSet, FormulaSet, PropSet, BitEncoding(..))
import qualified Pomc.Data as D
import Pomc.PropConv (APType, convPropTokens)

import Data.Maybe (fromJust, fromMaybe, isNothing)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (foldl', sortOn)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M

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


type EncPrecFunc = EncodedSet -> EncodedSet -> Maybe Prec

fromStructEnc :: BitEncoding -> [StructPrecRel APType] -> (EncPrecFunc, PropSet)
fromStructEnc bitenc sprs = (\s1 s2 -> M.lookup (structLabel s1, structLabel s2) relMap, sl)
  where sl = S.fromList $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) sprs
        maskSL = D.inputSuchThat bitenc (flip S.member sl)
        structLabel s = s `D.intersect` maskSL
        relMap = M.fromList $ map (\(sl1, sl2, pr) ->
                                     ((encodeProp sl1, encodeProp sl2), pr)) sprs
        encodeProp = D.encodeInput bitenc . S.singleton


type Input = EncodedSet
type Atom = EncodedSet

data State = State
    { current   :: Atom
    , pending   :: EncodedSet
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
  show (State c p xl xe xr) = "\n{ C: "  ++ show c  ++
                              "\n, P: "  ++ show p  ++
                              "\n, XL: " ++ show xl ++
                              "\n, X=: " ++ show xe ++
                              "\n, XR: " ++ show xr ++
                              "\n}"

showState :: BitEncoding -> State -> String
showState bitenc (State c p xl xe xr) =
  "\n{ C: "  ++ showAtom bitenc c  ++
  "\n, P: "  ++ showAtom bitenc p  ++
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


compProps :: BitEncoding -> EncodedSet -> Input -> Bool
compProps bitenc fset pset = D.extractInput bitenc fset == pset

closure :: Formula APType -> [Prop APType] -> FormulaSet
closure phi otherProps = let propClos = concatMap (closList . Atomic) (End : otherProps)
                             phiClos  = closList phi
                         in S.fromList (propClos ++ phiClos)
  where
    chainNextExp pset g = concatMap (\p -> [ ChainNext (PS.singleton p) g
                                           , Not (ChainNext (PS.singleton p) g)
                                           ]) (PS.toList pset)
    chainBackExp pset g = concatMap (\p -> [ ChainBack (PS.singleton p) g
                                           , Not (ChainBack (PS.singleton p) g)
                                           ]) (PS.toList pset) ++
                          if Take `PS.member` pset
                            then [ PrecBack  (PS.singleton Yield) g
                                 , ChainBack (PS.singleton Yield) g
                                 , Not $ PrecBack  (PS.singleton Yield) g
                                 , Not $ ChainBack (PS.singleton Yield) g
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
                 , ChainBack (PS.singleton Yield) T
                 , HierNextYield (HierUntilYield g h)
                 , Not $ T
                 , Not $ ChainBack (PS.singleton Yield) T
                 , Not $ HierNextYield (HierUntilYield g h)
                 ]
    hsyExp g h = [ T
                 , ChainBack (PS.singleton Yield) T
                 , HierBackYield (HierSinceYield g h)
                 , Not $ T
                 , Not $ ChainBack (PS.singleton Yield) T
                 , Not $ HierBackYield (HierSinceYield g h)
                 ]
    hutExp g h = [ T
                 , ChainNext (PS.singleton Take) T
                 , HierNextTake (HierUntilTake g h)
                 , Not $ T
                 , Not $ ChainNext (PS.singleton Take) T
                 , Not $ HierNextTake (HierUntilTake g h)
                 ] ++ hntExp (HierUntilTake g h)
    hstExp g h = [ T
                 , ChainNext (PS.singleton Take) T
                 , HierBackTake (HierSinceTake g h)
                 , Not $ T
                 , Not $ ChainNext (PS.singleton Take) T
                 , Not $ HierBackTake (HierSinceTake g h)
                 ] ++ hbtExp (HierSinceTake g h)
    evExp g = [ PrecNext (PS.fromList [Yield, Equal, Take]) (Eventually' g)
              , Not $ PrecNext (PS.fromList [Yield, Equal, Take]) (Eventually' g)
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

makeBitEncoding :: FormulaSet -> BitEncoding
makeBitEncoding clos =
  let pclos = S.filter (not . negative) clos

      fetch vec i = vec V.! i

      -- Mapping between positive formulas and bits
      pFormulaClos = S.filter (not . atomic) pclos
      pFormulaVec = V.fromList . S.toAscList $ pFormulaClos
      pFormulaMap = M.fromList (zip (S.toAscList pFormulaClos) [0..])

      -- Mapping between positive atoms and bits
      pAtomicClos = S.filter atomic pclos
      pAtomicIndices = sortOn snd $
                       map (\p -> (p, unwrapProp p)) $
                       S.toAscList pAtomicClos
      pAtomicVec = V.fromList $ map fst pAtomicIndices
      pAtomicMap = M.fromList pAtomicIndices

      unwrapProp :: Formula APType -> Int
      unwrapProp (Atomic End) = 0
      unwrapProp (Atomic (Prop n)) = fromIntegral n

      -- Mapping between positive closure and bits
      pClosVec = pAtomicVec V.++ pFormulaVec
      pClosLookup phi = fromJust $ M.lookup phi pClosMap
        where pClosMap = pAtomicMap `M.union` M.map (V.length pAtomicVec +) pFormulaMap

  in BitEncoding { D.fetch = fetch pClosVec
                 , D.index = pClosLookup
                 , D.width = V.length pClosVec
                 , D.propBits = V.length pAtomicVec
                 }


atoms :: BitEncoding -> FormulaSet -> Set (PropSet) -> [Atom]
atoms bitenc clos inputSet =
  let validPropSets = S.insert (S.singleton End) inputSet

      -- Make power set of AP
      atomics = map (D.encodeInput bitenc) $ S.toList validPropSets

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
                       let eset' = D.joinInputFormulas easet eset
                       guard (consistent eset')
                       return eset'
        in as SQ.>< (SQ.fromList combs)

  in toList $ if width bitenc - propBits bitenc == 0
              then SQ.fromList atomics
              else foldl' prependCons SQ.empty (D.generateFormulas bitenc)

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
                                                                  PS.size pset > 1 &&
                                                                  present pset g &&
                                                                  not (D.member bitenc f set)]
  where present pset g = any (\p -> D.member bitenc (ChainNext (PS.singleton p) g) set)
                             (PS.toList pset)
        consSet (ChainNext pset g) = PS.size pset > 1 && not (present pset g)
        consSet _ = False

chainBackCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
chainBackCons bitenc clos set = not (D.any bitenc consSet set)
                                &&
                                null [f | f@(ChainBack pset g) <- S.toList clos,
                                                                  PS.size pset > 1 &&
                                                                  present pset g &&
                                                                  not (D.member bitenc f set)]
  where present pset g = any (\p -> D.member bitenc (ChainBack (PS.singleton p) g) set)
                             (PS.toList pset)
        consSet (ChainBack pset g) = PS.size pset > 1 && not (present pset g)
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
          (D.member bitenc h set && D.member bitenc (ChainBack (PS.singleton Yield) T) set)
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
          (D.member bitenc h set && D.member bitenc (ChainBack (PS.singleton Yield) T) set)
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
          (D.member bitenc h set && D.member bitenc (ChainNext (PS.singleton Take) T) set)
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
          (D.member bitenc h set && D.member bitenc (ChainNext (PS.singleton Take) T) set)
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
          (D.member bitenc (PrecNext (PS.fromList [Yield, Equal, Take]) ev) set)
        consSet f@(Eventually' g) = not $ present f g
        consSet _ = False

pendCombs :: BitEncoding -> FormulaSet -> Set (EncodedSet, Bool, Bool, Bool)
pendCombs bitenc clos =
  let cnfs  = [f | f@(ChainNext pset _) <- S.toList clos, (PS.size pset) == 1]
      cbfs  = [f | f@(ChainBack pset _) <- S.toList clos, (PS.size pset) == 1]
      hnyfs = [f | f@(HierNextYield _)  <- S.toList clos]
      hntfs = [f | f@(HierNextTake _)   <- S.toList clos]
      hbtfs = [f | f@(HierBackTake _)   <- S.toList clos]
      hthfs = [f | f@(HierTakeHelper _) <- S.toList clos]
  in S.foldl' S.union S.empty .
     S.map (S.fromList . combs . (D.encode bitenc)) $
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
                                                        pset == (PS.singleton Yield)]
  in [State ia (D.encode bitenc ip) True False False | ia <- compAtoms,
                                                       ip <- S.toList (S.powerSet cnyfSet)]

resolve :: i -> [(i -> Bool, b)] -> [b]
resolve info conditionals = snd . unzip $ filter (\(cond, _) -> cond info) conditionals

deltaRules :: BitEncoding -> FormulaSet -> EncPrecFunc -> (RuleGroup, RuleGroup, RuleGroup)
deltaRules bitenc cl precFunc =
  let shiftGroup = RuleGroup
        { ruleGroupPrs  = resolve cl [ (const True, xlShiftPr)
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
        , ruleGroupFcrs = resolve cl [ (pnCond, pnShiftFcr)
                                     , (pbCond, pbShiftFcr)
                                     ]
        , ruleGroupFprs = resolve cl [ (const True, xrShiftFpr)
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
        , ruleGroupFrs  = resolve cl []
        }
      pushGroup = RuleGroup
        { ruleGroupPrs  = resolve cl [ (const True, xlPushPr)
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
        , ruleGroupFcrs = resolve cl [ (pnCond, pnPushFcr)
                                     , (pbCond, pbPushFcr)
                                     ]
        , ruleGroupFprs = resolve cl [ (const True, xrPushFpr)
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
        , ruleGroupFrs  = resolve cl []
        }
      popGroup = RuleGroup
        { ruleGroupPrs  = resolve cl [ (const True, xlPopPr)
                                     , (const True, xePopPr)
                                     , (cneCond,    cnePopPr)
                                     , (cntCond,    cntPopPr)
                                     , (hnyCond,    hnyPopPr)
                                     ]
        , ruleGroupFcrs = resolve cl []
        , ruleGroupFprs = resolve cl [ (const True, xrPopFpr)
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
        , ruleGroupFrs  = resolve cl [(hbyCond, hbyPopFr)]
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
      let pCurr = current $ fcrState info
          props = fromJust (fcrProps info)
          fCurr = fcrFutureCurr info

          maskPn = D.suchThat bitenc checkPn
          checkPn (PrecNext _ _) = True
          checkPn _ = False

          maskPnny = D.suchThat bitenc (checkPnnp Yield)
          maskPnne = D.suchThat bitenc (checkPnnp Equal)
          maskPnnt = D.suchThat bitenc (checkPnnp Take)
          checkPnnp prec (PrecNext pset _) = prec `PS.notMember` pset
          checkPnnp prec _ = False

          precComp Yield = D.null $ D.intersect pCurr maskPnny
          precComp Equal = D.null $ D.intersect pCurr maskPnne
          precComp Take  = D.null $ D.intersect pCurr maskPnnt

          fsComp prec = pCurrPnfs == checkSet
            where pCurrPnfs = D.intersect pCurr maskPn
                  checkSet = D.encode bitenc $ S.filter checkSetPred closPn
                  checkSetPred (PrecNext pset g) = prec `PS.member` pset && D.member bitenc g fCurr
                  checkSetPred _ = False
                  closPn = S.filter checkPn cl

      in case precFunc props (D.extractInput bitenc fCurr) of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pnShiftFcr = pnPushFcr
    --

    -- PB rules
    pbCond clos = not (null [f | f@(PrecBack _ _) <- S.toList clos])

    pbPushFcr info =
      let pCurr = current $ fcrState info
          props = fromJust (fcrProps info)
          fCurr = fcrFutureCurr info

          maskPb = D.suchThat bitenc checkPb
          checkPb (PrecBack _ _) = True
          checkPb _ = False

          maskPbny = D.suchThat bitenc (checkPbnp Yield)
          maskPbne = D.suchThat bitenc (checkPbnp Equal)
          maskPbnt = D.suchThat bitenc (checkPbnp Take)
          checkPbnp prec (PrecBack pset _) = prec `PS.notMember` pset
          checkPbnp prec _ = False

          precComp Yield = D.null $ D.intersect fCurr maskPbny
          precComp Equal = D.null $ D.intersect fCurr maskPbne
          precComp Take  = D.null $ D.intersect fCurr maskPbnt

          fsComp prec = fCurrPbfs == checkSet
            where fCurrPbfs = D.intersect fCurr maskPb
                  checkSet = D.encode bitenc $ S.filter checkSetPred closPb
                  checkSetPred (PrecBack pset g) = prec `PS.member` pset && D.member bitenc g pCurr
                  checkSetPred _ = False
                  closPb = S.filter checkPb cl

      in case precFunc props (D.extractInput bitenc fCurr) of
           Nothing   -> False
           Just prec -> precComp prec && fsComp prec

    pbShiftFcr = pbPushFcr
    --

    -- CNY
    maskCny = D.suchThat bitenc checkCny
    checkCny (ChainNext pset _) = pset == PS.singleton Yield
    checkCny _ = False

    cnyCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == PS.singleton Yield])

    cnyPushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          pCurrCnyfs = D.intersect pCurr maskCny
          fPendCnyfs = D.intersect fPend maskCny

      in if fXl
           then pCurrCnyfs == fPendCnyfs
           else D.null pCurrCnyfs

    cnyShiftFpr = cnyPushFpr

    cnyPopFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          ppPend = pending $ fromJust (fprPopped info)
          ppPendCnyfs = D.intersect maskCny ppPend

          cnyClos = S.filter checkCny cl
          pCheckSet = D.encode bitenc $
                      S.filter (\(ChainNext _ g) -> D.member bitenc g pCurr) cnyClos

          fCheckSet = D.intersect fPend maskCny

          checkSet = D.union pCheckSet fCheckSet
      in if fXl
           then ppPendCnyfs == checkSet
           else D.null ppPendCnyfs
    --

    -- CNE rules
    maskCne = D.suchThat bitenc checkCne
    checkCne (ChainNext pset _) = pset == PS.singleton Equal
    checkCne _ = False

    cneCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == PS.singleton Equal])

    cnePushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCnefs = D.intersect maskCne fPend
          pCurrCnefs = D.intersect maskCne pCurr
      in if fXl
           then pCurrCnefs == fPendCnefs
           else D.null pCurrCnefs

    cneShiftFpr = cnePushFpr

    cnePopPr info =
      let pPend = pending (prState info)
          pPendCnefs = D.intersect pPend maskCne
      in D.null pPendCnefs

    cnePopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCnefs = D.intersect ppPend maskCne
          fPendCnefs = D.intersect fPend maskCne
      in ppPendCnefs == fPendCnefs

    cneShiftPr info =
      let pCurr = current $ prState info
          pPend = pending $ prState info
          pPendCnefs = D.intersect pPend maskCne

          cneClos = S.filter checkCne cl
          pCheckList = D.encode bitenc $
                       S.filter (\(ChainNext _ g) -> D.member bitenc g pCurr) cneClos

      in pCheckList == pPendCnefs
    --

    -- CNT rules
    maskCnt = D.suchThat bitenc checkCnt
    checkCnt (ChainNext pset _) = pset == PS.singleton Take
    checkCnt _ = False

    cntCond clos = not (null [f | f@(ChainNext pset _) <- S.toList clos,
                                                          pset == PS.singleton Take])

    cntPushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info
          fPendCntfs = D.intersect fPend maskCnt
          pCurrCntfs = D.intersect pCurr maskCnt
      in if fXl
           then pCurrCntfs == fPendCntfs
           else D.null pCurrCntfs

    cntShiftFpr = cntPushFpr

    cntPopPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pPendCntfs = D.intersect pPend maskCnt

          cntClos = S.filter checkCnt cl
          pCheckList = D.encode bitenc $
                       S.filter (\(ChainNext _ g) -> D.member bitenc g pCurr) cntClos

      in pCheckList == pPendCntfs

    cntPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCntfs = D.intersect ppPend maskCnt
          fPendCntfs = D.intersect fPend maskCnt
      in ppPendCntfs == fPendCntfs

    cntShiftPr info =
      let pPend = pending (prState info)
          pPendCntfs = D.intersect pPend maskCnt
      in D.null pPendCntfs
    --

    -- CBY
    maskCby = D.suchThat bitenc checkCby
    checkCby (ChainBack pset _) = pset == PS.singleton Yield
    checkCby _ = False

    cbyCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == PS.singleton Yield])

    cbyPushPr info =
      let pCurr = current $ prState info
          pPend = pending $ prState info
          pXr = afterPop (prState info)
          pCurrCbyfs = D.intersect pCurr maskCby
          pPendCbyfs = D.intersect pPend maskCby
      in if pXr
           then pCurrCbyfs == pPendCbyfs
           else D.null pCurrCbyfs

    cbyShiftPr info =
      let pCurr = current $ prState info
      in D.null $ D.intersect pCurr maskCby

    cbyPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCbyfs = D.intersect ppPend maskCby
          fPendCbyfs = D.intersect fPend maskCby
      in ppPendCbyfs == fPendCbyfs

    cbyPushFpr info =
      let pCurr = current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendCbyfs = D.intersect fPend maskCby

          cbyClos = S.filter checkCby cl
          pCheckSet = D.encode bitenc $
                      S.filter (\(ChainBack _ g) -> D.member bitenc g pCurr) cbyClos

      in fPendCbyfs == pCheckSet

    cbyShiftFpr = cbyPushFpr
    --

    -- CBE
    maskCbe = D.suchThat bitenc checkCbe
    checkCbe (ChainBack pset _) = pset == PS.singleton Equal
    checkCbe _ = False

    cbeCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == PS.singleton Equal])

    cbeShiftPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrCbefs = D.intersect pCurr maskCbe
          pPendCbefs = D.intersect pPend maskCbe
      in if pXr
           then pCurrCbefs == pPendCbefs
           else D.null pCurrCbefs

    cbePushPr info =
      let pCurr = current $ prState info
      in D.null $ D.intersect pCurr maskCbe

    cbePopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendCbefs = D.intersect ppPend maskCbe
          fPendCbefs = D.intersect fPend maskCbe
      in ppPendCbefs == fPendCbefs

    cbePushFpr info =
      let pCurr = current $ fprState info
          (fPend, fXl, _, _) = fprFuturePendComb info

          fPendCbefs = D.intersect fPend maskCbe

          cbeClos = S.filter checkCbe cl
          pCheckSet = D.encode bitenc $
                      S.filter (\(ChainBack _ g) -> D.member bitenc g pCurr) cbeClos

      in fPendCbefs == pCheckSet

    cbeShiftFpr = cbePushFpr
    --

    -- CBT
    maskCbt = D.suchThat bitenc checkCbt
    checkCbt (ChainBack pset _) = pset == PS.singleton Take
    checkCbt _ = False

    cbtCond clos = not (null [f | f@(ChainBack pset _) <- S.toList clos,
                                                          pset == PS.singleton Take])

    cbtPushFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info
          fPendCbtfs = D.intersect fPend maskCbt
      in D.null fPendCbtfs

    cbtShiftFpr = cbtPushFpr

    cbtPushPr info =
      let pCurr = current $ prState info
          pPend = pending $ prState info
          pXr = afterPop $ prState info
          pCurrCbtfs = D.intersect pCurr maskCbt
          pPendCbtfs = D.intersect pPend maskCbt
      in if pXr
           then pCurrCbtfs == pPendCbtfs
           else D.null pCurrCbtfs

    cbtShiftPr = cbtPushPr

    cbtPopFpr info =
      let pPend = pending (fprState info)
          (fPend, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)
          pPendCbtfs = D.intersect pPend maskCbt
          fPendCbtfs = D.intersect fPend maskCbt

          ppCurrCbyfs = D.intersect ppCurr maskCby
          ppCurrPbyfs = D.intersect ppCurr maskPby
          cby f = ChainBack (PS.singleton Yield) f
          pby f = PrecBack (PS.singleton Yield) f
          yieldCheckSet = D.filter
            bitenc
            (\(ChainBack _ f) -> D.member bitenc (cby f) ppCurrCbyfs
                                 || D.member bitenc (pby f) ppCurrPbyfs)
            maskCbt
          takeCheckSet = pPendCbtfs
          checkSet = yieldCheckSet `D.union` takeCheckSet

          maskPby = D.suchThat bitenc checkPby
          checkPby (PrecBack pset _) = pset == PS.singleton Yield
          checkPby _ = False
      in if fXl || fXe
           then pPendCbtfs == fPendCbtfs
           else checkSet == fPendCbtfs
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
      let pCurr = current $ prState info
          pPend = pending $ prState info
          pXr = afterPop $ prState info
          pPendHnyfs = D.intersect pPend maskHny

          hnyClos = S.filter checkHny cl
          checkSet = D.encode bitenc $
                     S.filter (\(HierNextYield g) -> D.member bitenc g pCurr) hnyClos
      in if pXr
           then checkSet == pPendHnyfs
           else D.null pPendHnyfs

    hnyPopFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)
          ppXr = afterPop $ fromJust (fprPopped info)
          fPendHnyfs = D.intersect fPend maskHny
          ppCurrHnyfs = D.intersect ppCurr maskHny
      in if ppXr
           then ppCurrHnyfs == fPendHnyfs
           else True

    hnyPopPr info =
      let pPend = pending (prState info)
          pPendHnyfs = D.intersect pPend maskHny
      in D.null pPendHnyfs

    hnyShiftPr info =
      let pCurr = current $ prState info
          pPend = pending $ prState info
          pCurrHnyfs = D.intersect pCurr maskHny
          pPendHnyfs = D.intersect pPend maskHny
      in D.null pCurrHnyfs && D.null pPendHnyfs
    --

    -- HBY
    maskHby = D.suchThat bitenc checkHby
    checkHby (HierBackYield _) = True
    checkHby _ = False

    hbyCond clos = not (null [f | f@(HierBackYield _) <- S.toList clos])

    hbyPushPr info =
      let pCurr = current $ prState info
          pXl = mustPush $ prState info
          pXr = afterPop $ prState info
      in if not $ D.null $ D.intersect pCurr maskHby
         then pXl && pXr
         else True

    hbyShiftPr info =
      let pCurr = current $ prState info
      in D.null $ D.intersect pCurr maskHby

    hbyPopFr info =
      let (_, fXl, _, _) = frFuturePendComb info
          fCurr = frFutureCurr info
          ppCurr = current $ fromJust (frPopped info)
          ppXr = afterPop $ fromJust (frPopped info)
          fCurrHbyfs = D.intersect fCurr maskHby

          hbyClos = S.filter checkHby cl
          checkSet = D.encode bitenc $
                     S.filter (\(HierBackYield g) -> D.member bitenc g ppCurr) hbyClos
      in if fXl
         then if ppXr
              then fCurrHbyfs == checkSet
              else D.null fCurrHbyfs
         else True
    --

    -- HNT
    maskHnt = D.suchThat bitenc checkHnt
    checkHnt (HierNextTake _) = True
    checkHnt _ = False
    hntClos = S.filter checkHnt cl

    hntCond clos = not (null [f | f@(HierNextTake _) <- S.toList clos])

    hntPopFpr1 info =
      let (fPend, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          fPendHntfs = D.intersect fPend maskHnt

          hth = HierTakeHelper
          checkSet = D.encode bitenc $
                     S.filter (\(HierNextTake g) -> D.member bitenc (hth g) ppCurr) hntClos

      in if not fXl && not fXe
           then fPendHntfs == checkSet
           else True

    hntPopFpr2 info =
      let pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          pPendHntfs = D.intersect pPend maskHnt

          hth = HierTakeHelper
          checkSet = D.encode bitenc $
                     S.filter (\f -> D.member bitenc (hth f) ppCurr) hntClos

      in if not fXl && not fXe
           then pPendHntfs == checkSet
           else True

    hntPopFpr3 info =
      let pPend = pending (fprState info)
          (_, _, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          hth = HierTakeHelper
          checkSet = S.filter (\f -> D.member bitenc (hth f) ppCurr) hntClos

      in if not (null checkSet)
           then not fXe
           else True

    hntPushFpr1 info =
      let pCurr = current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
      in if not $ D.null $ D.intersect pCurr maskHnt
         then fXl
         else True

    hntShiftFpr1 = hntPushFpr1

    hntPushFpr2 info =
      let (fPend, _, _, _) = fprFuturePendComb info
          fPendHntfs = D.intersect fPend maskHnt
      in D.null fPendHntfs

    hntShiftFpr2 = hntPushFpr2
    --

    -- HBT
    maskHbt = D.suchThat bitenc checkHbt
    checkHbt (HierBackTake _) = True
    checkHbt _ = False
    hbtClos = S.filter checkHbt cl

    hbtCond clos = not (null [f | f@(HierBackTake _) <- S.toList clos])

    hbtPopFpr1 info =
      let pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          pPendHbtfs = D.intersect pPend maskHbt

          hth = HierTakeHelper
          checkSet = D.encode bitenc $
                     S.filter (\(HierBackTake g) -> D.member bitenc (hth g) ppCurr) hbtClos

      in if not fXl && not fXe
           then pPendHbtfs == checkSet
           else True

    hbtPopFpr2 info =
      let (fPend, fXl, _, _) = fprFuturePendComb info
          ppCurr = current $ fromJust (fprPopped info)

          fPendHbtfs = D.intersect fPend maskHbt

          hth = HierTakeHelper
          checkSet = D.encode bitenc $
                     S.filter (\f -> D.member bitenc (hth f) ppCurr) hbtClos

      in if not fXl
           then fPendHbtfs == checkSet
           else True

    hbtPopFpr3 info =
      let pPend = pending (fprState info)
          (_, fXl, fXe, _) = fprFuturePendComb info
          pPendHbtfs = D.intersect pPend maskHbt
      in if not (D.null pPendHbtfs)
           then not fXl && not fXe
           else True

    hbtPushFpr info =
      let pCurr = current $ fprState info
          (_, fXl, _, _) = fprFuturePendComb info
      in if not $ D.null $ D.intersect pCurr maskHbt
         then fXl
         else True

    hbtShiftFpr = hbtPushFpr

    hbtPushPr info =
      let pPend = pending (prState info)
          pPendHbtfs = D.intersect pPend maskHbt
      in D.null pPendHbtfs

    hbtShiftPr = hbtPushPr
    --

    -- HTH
    maskHth = D.suchThat bitenc checkHth
    checkHth (HierTakeHelper _) = True
    checkHth _ = False

    hthCond clos = not (null [f | f@(HierTakeHelper _) <- S.toList clos])

    hthPushPr info =
      let pCurr = current $ prState info
          pPend = pending (prState info)
          pXr = afterPop (prState info)
          pCurrHthfs = D.intersect pCurr maskHth
          pPendHthfs = D.intersect pPend maskHth
      in pCurrHthfs == pPendHthfs

    hthShiftPr info =
      let pCurr = current $ prState info
      in D.null $ D.intersect pCurr maskHth

    hthPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info)
          (fPend, _, _, _) = fprFuturePendComb info
          ppPendHthfs = D.intersect ppPend maskHth
          fPendHthfs = D.intersect fPend maskHth
      in ppPendHthfs == fPendHthfs

    hthPushFpr info =
      let pCurr = current $ fprState info
          (fPend, _, _, _) = fprFuturePendComb info
          fPendHthfs = D.intersect fPend maskHth

          hthClos = S.filter checkHth cl
          pCheckSet = D.encode bitenc $
                      S.filter (\(HierTakeHelper g) -> D.member bitenc g pCurr) hthClos

      in fPendHthfs == pCheckSet

    hthShiftFpr = hthPushFpr
    --

data PrInfo = PrInfo
  { prState     :: State
  , prProps     :: Maybe (Input)
  , prPopped    :: Maybe (State)
  , prNextProps :: Maybe (Input)
  }
data FcrInfo = FcrInfo
  { fcrState      :: State
  , fcrProps      :: Maybe (Input)
  , fcrPopped     :: Maybe (State)
  , fcrFutureCurr :: Atom
  , fcrNextProps  :: Maybe (Input)
  }
data FprInfo = FprInfo
  { fprState          :: State
  , fprProps          :: Maybe (Input)
  , fprPopped         :: Maybe (State)
  , fprFuturePendComb :: (EncodedSet, Bool, Bool, Bool)
  , fprNextProps      :: Maybe (Input)
  }
data FrInfo = FrInfo
  { frState          :: State
  , frProps          :: Maybe (Input)
  , frPopped         :: Maybe (State)
  , frFutureCurr     :: Atom
  , frFuturePendComb :: (EncodedSet, Bool, Bool, Bool)
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

augDeltaRules :: BitEncoding -> FormulaSet -> EncPrecFunc -> (RuleGroup, RuleGroup, RuleGroup)
augDeltaRules bitenc cl prec =
  let (shiftrg, pushrg, poprg) = deltaRules bitenc cl prec
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
      where info = PrInfo { prState     = state,
                            prProps     = mprops,
                            prPopped    = mpopped,
                            prNextProps = mnextprops
                          }

    vas = filter valid nextAtoms
      where makeInfo curr = FcrInfo { fcrState      = state,
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
      where makeInfo pendComb = FprInfo { fprState          = state,
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
      where makeInfo curr pendComb = FrInfo { frState          = state,
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
  && (not $ D.any bitenc future currFset) -- TODO: mask this
  && pendComb
  where currFset = current s
        currPend = pending s
        pendComb = currPend == (D.intersect currPend maskCbt)
        -- only ChainBack Take formulas are allowed

        maskCbt = D.suchThat bitenc checkCbt
        checkCbt (ChainBack pset _) = pset == PS.singleton Take
        checkCbt _ = False

        debug = id
        --debug = DT.trace ("\nIs state final?" ++ show s) . DT.traceShowId

check :: Formula APType
      -> [StructPrecRel APType]
      -> [PropSet]
      -> Bool
check phi sprs ts =
  debug $ run
            prec
            is
            (isFinal bitenc)
            (deltaShift cl as pcs prec shiftRules)
            (deltaPush  cl as pcs prec  pushRules)
            (deltaPop   cl as pcs prec   popRules)
            encTs
  where nphi = normalize . toReducedPotl $ phi
        tsprops = S.toList $ foldl' (S.union) S.empty (sl:ts)
        inputSet = foldl' (flip S.insert) S.empty ts
        encTs = map (D.encodeInput bitenc) ts

        cl = closure nphi tsprops
        bitenc = makeBitEncoding cl
        (prec, sl) = fromStructEnc bitenc sprs
        as = atoms bitenc cl inputSet
        pcs = pendCombs bitenc cl
        is = initials nphi cl (as, bitenc)
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec
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
  in check tphi tprecr tts


fastcheck :: Formula APType
          -> [StructPrecRel APType]
          -> [PropSet]
          -> Bool
fastcheck phi sprs ts =
  debug $ augRun
            prec
            is
            (isFinal bitenc)
            (augDeltaShift cl as pcs prec shiftRules)
            (augDeltaPush  cl as pcs prec  pushRules)
            (augDeltaPop   cl as pcs prec   popRules)
            encTs
  where nphi = normalize . toReducedPotl $ phi

        tsprops = S.toList $ foldl' (S.union) S.empty (sl:ts)
        inputSet = foldl' (flip S.insert) S.empty ts
        encTs = map (D.encodeInput bitenc) ts

        cl = closure nphi tsprops
        bitenc = makeBitEncoding cl
        (prec, sl) = fromStructEnc bitenc sprs
        as = atoms bitenc cl inputSet
        pcs = pendCombs bitenc cl
        is = filter compInitial (initials nphi cl (as, bitenc))
        (shiftRules, pushRules, popRules) = augDeltaRules bitenc cl prec

        compInitial s = fromMaybe True $
                          (compProps bitenc) <$> (Just . current) s <*> safeHead encTs

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
                              Nothing    -> D.encodeInput bitenc $ S.singleton End

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
  in fastcheck tphi tprecr tts


makeOpa :: (Checkable f)
        => f APType
        -> ([Prop APType], [Prop APType])
        -> [StructPrecRel APType]
        -> (BitEncoding
           , EncPrecFunc
           , [State]
           , State -> Bool
           , State -> Input -> [State]
           , State -> Input -> [State]
           , State -> State -> [State]
           )
makeOpa phi (sls, als) sprs = (bitenc
                              , prec
                              , is
                              , isFinal bitenc
                              , deltaPush  cl as pcs prec pushRules
                              , deltaShift cl as pcs prec shiftRules
                              , deltaPop   cl as pcs prec popRules
                              )
  where nphi = normalize . toReducedPotl $ phi
        tsprops = sls ++ als
        inputSet = S.fromList [S.fromList (sl:alt) | sl <- sls, alt <- filterM (const [True, False]) als]

        cl = closure nphi tsprops
        bitenc = makeBitEncoding cl
        (prec, _) = fromStructEnc bitenc sprs
        as = atoms bitenc cl inputSet
        pcs = pendCombs bitenc cl
        is = initials nphi cl (as, bitenc)
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec

        deltaShift clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush clos atoms pcombs prec rgroup state props = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop clos atoms pcombs prec rgroup state popped = fstates
          where fstates = delta rgroup prec clos atoms pcombs state
                                Nothing (Just popped) Nothing
