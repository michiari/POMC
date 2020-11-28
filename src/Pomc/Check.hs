{-# LANGUAGE DeriveGeneric #-}

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
                  , Input
                  , Atom
                  , State(..)
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import qualified Pomc.Prec as PS (singleton, size, member, notMember, fromList, toList)
import Pomc.Opa (run, augRun)
import Pomc.RPotl (Formula(..), negative, negation, atomic, normalize, future)
import Pomc.Util (safeHead, xor, implies, iff)
import Pomc.Data (EncodedSet, FormulaSet, PropSet, BitEncoding(..))
import qualified Pomc.Data as D
import Pomc.PropConv (APType, convPropTokens)

import Data.Maybe (fromJust, fromMaybe, isNothing)

import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.Vector as V

import Data.List (foldl', sortOn)

import qualified Data.HashMap.Strict as M

import Control.Monad (guard, filterM)

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
-- generate an EncPrecFunc from a StructPrecRel
fromStructEnc :: BitEncoding -> [StructPrecRel APType] -> (EncPrecFunc, PropSet)
fromStructEnc bitenc sprs = (\s1 s2 -> M.lookup (structLabel s1, structLabel s2) relMap, sl)
  where 
        --a set of all structural labels whose prec relation is defined at least once (fromList removes duplicates)
        sl = S.fromList $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) sprs
        -- an encoded Atom where all ones corresponds to members of previous set
        maskSL = D.inputSuchThat bitenc (flip S.member sl)
        -- a function which makes a bitwise AND between a parameter Atom and the mask
        structLabel s = s `D.intersect` maskSL
        --map the relation between props into a relation between EncodedAtoms
        relMap = M.fromList $ map (\(sl1, sl2, pr) ->
                                     ((encodeProp sl1, encodeProp sl2), pr)) sprs
        --encode a single atomic proposition into an EncodedAtom
        encodeProp = D.encodeInput bitenc . S.singleton


type Input = EncodedSet
type Atom = EncodedSet

data State = State
    { current   :: Atom
    , pending   :: EncodedSet
    , mustPush  :: !Bool
    , mustShift :: !Bool
    , afterPop  :: !Bool
    } deriving (Generic, Ord, Eq)

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


-- generate a closure ( phi= input formula of makeOpa, otherProps = AP set of the language)
closure :: Formula APType -> [Prop APType] -> FormulaSet
closure phi otherProps = let propClos = concatMap (closList . Atomic) (End : otherProps)
                             phiClos  = closList phi
                         in S.fromList (propClos ++ phiClos)
  where
    xbuExpr g = AuXBack Down g ++ Not $ AuxBack Down g
    hndExpr g = AuXBack Down g ++ Not (AuxBack Down g) ++ AuXBack Down (HNext Down g) ++ Not $ AuXBack Down (HNext Down g)
    hbdExpr g = Auxback Down g ++ Not (AuxBack Down g) ++ AuXBack Down (HBack Down g) ++ Not $ AuXBack Down (HBack Down g)
    untilExpr dir g h = 
    sinceExpr g h =
    huuExpr g h = XBack Down T ++ Not (XBack Down T) ++ T ++ Not T ++ HNext Up (HUntil Up g h) ++ Not $ HNext Up (HUntil Up g h)
    hsuExpr g h = XBack Down T ++ Not (XBack Down T) ++ T ++ Not T ++ HBack Up (HSince Up g h) ++ Not $ HBack Up (HSince Up g h)
    hudExpr g h = XNext Up T   ++ Not (XNext Up T)   ++ T ++ Not T ++ HNext Down (HUntil Down g h) ++ Not $ HNext Down (HUntil Down g h)
    hsdExpr g h = XNext Up T   ++ Not (XNext Up T)   ++ T ++ Not T ++ HBack Down (HSince Down g h) ++ Not $ HBack Down (HSince Down g h)
    evExpr g =
    closList f = case f of
      T                  -> [f, Not f]
      Atomic _           -> [f, Not f]
      Not g              -> [f] ++ closList g
      Or g h             -> [f, Not f] ++ closList g ++ closList h
      And g h            -> [f, Not f] ++ closList g ++ closList h
      Xor g h            -> [f, Not f] ++ closList g ++ closList h
      Implies g h        -> [f, Not f] ++ closList g ++ closList h
      Iff g h            -> [f, Not f] ++ closList g ++ closList h
      PNext _ g          -> [f, Not f] ++ closList g
      PBack _ g          -> [f, Not f] ++ closList g 
      XNext _ g          -> [f, Not f] ++ closList g 
      XBack Down g       -> [f, Not f] ++ closList g 
      XBack Up g         -> [f, Not f] ++ closList g ++ xbuExpr g
      HNext Down g       -> [f, Not f] ++ closList g ++ hndExpr g
      HNext Up g         -> [f, Not f] ++ closList g  
      HBack Down g       -> [f, Not f] ++ closList g ++ hbdExpr g
      HBack Up g         -> [f, Not f] ++ closList g 
      Until dir g h        -> [f, Not f] ++ closList g ++ closList h ++ untilExpr dir g h
      Since _ g h        -> [f, Not f] ++ closList g ++ closList h ++ sinceExpr g h 
      HUntil Down g h    -> [f, Not f] ++ closList g ++ closList h
      HUntil Up g h      -> [f, Not f] ++ closList g ++ closList h ++ huuExpr g h
      HSince Down g h    -> [f, Not f] ++ closList g ++ closList h ++ hudExpr g h
      HSince Up g h      -> [f, Not f] ++ closList g ++ closList h + hsuExpr g h 
      HSince Down g h    -> [f, Not f] ++ closList g ++ closList h + hsdExpr g h 
      Eventually g       -> [f, Not f] ++ closList g ++ evExp g 
      Always g           -> [f, Not f] ++ closList g ++ alwExp g
      AuXBack Down g     -> [f, Not f] ++ closList g


-- given a closure of phi, generate a bitEncoding
makeBitEncoding :: FormulaSet -> BitEncoding
makeBitEncoding clos =
  let 
      -- positive formulas
      pclos = S.filter (not . negative) clos

      --function which return element at position i in vector vec
      fetchVec vec i = vec V.! i

      -- Mapping between positive formulas and bits
      pFormulaClos = S.filter (not . atomic) pclos
      pFormulaVec = V.fromList . S.toAscList $ pFormulaClos
      pFormulaMap = M.fromList (zip (S.toAscList pFormulaClos) [0..])

      -- Mapping between positive atoms and bits
      pAtomicClos = S.filter atomic pclos
      pAtomicSorted = sortOn unwrapProp $ S.toAscList pAtomicClos
      pAtomicVec = V.fromList pAtomicSorted
      pAtomicMap = M.fromList (zip pAtomicSorted [0..])

      unwrapProp :: Formula APType -> Int
      unwrapProp (Atomic End) = 0
      unwrapProp (Atomic (Prop n)) = fromIntegral n

      -- Mapping between positive closure and bits
      pClosVec = pAtomicVec V.++ pFormulaVec
      --index function of BitEncoding
      pClosLookup phi = fromJust $ M.lookup phi pClosMap
        where pClosMap = pAtomicMap `M.union` M.map (V.length pAtomicVec +) pFormulaMap

  in D.newBitEncoding (fetchVec pClosVec) pClosLookup (V.length pClosVec) (V.length pAtomicVec)

-- generate atoms from a bitEncoding, the closure of phi and the powerset of APs, excluded not valid sets
genAtoms :: BitEncoding -> FormulaSet -> Set (PropSet) -> [Atom]
genAtoms bitenc clos inputSet =
  let validPropSets = S.insert (S.singleton End) inputSet

      -- Map the powerset of APs into a set of EncodedAtoms
      atomics = map (D.encodeInput bitenc) $ S.toList validPropSets

      -- Consistency checks
      -- no checks needed for Atomic p
      -- no checks needed for Not g
      -- no checks needed for PNext dir g
      -- no checks needed for PBack dir g
      -- no checks needed for XNext dir g
      -- no checks needed for XBack dir g
      -- no checks needed for HNext dir g
      -- no checks needed for HBack dir g


      checks =
        [ onlyif (T `S.member` clos) (trueCons bitenc)
        , onlyif (not . null $ [f | f@(And _ _)          <- cl]) (andCons bitenc clos)
        , onlyif (not . null $ [f | f@(Or _ _)           <- cl]) (orCons bitenc clos)
        , onlyif (not . null $ [f | f@(Xor _ _)          <- cl]) (xorCons bitenc clos) 
        , onlyif (not . null $ [f | f@(Implies _ _)      <- cl]) (impliesCons bitenc clos) 
        , onlyif (not . null $ [f | f@(Iff _ _)          <- cl]) (iffCons bitenc clos) 
        , onlyif (not . null $ [f | f@(Until _ _ _)      <- cl]) (untilCons bitenc clos)
        , onlyif (not . null $ [f | f@(Since _ _ _)      <- cl]) (sinceCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Up _ _)    <- cl]) (hierUntilUpCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Up _ _)    <- cl]) (hierSinceUpCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Down  _ _) <- cl]) (hierUntilDownCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Down  _ _) <- cl]) (hierSinceDowneCons bitenc clos)
        , onlyif (not . null $ [f | f@(Eventually _)     <- cl]) (evCons bitenc clos)
        , onlyif (not . null $ [f | f@(Always _)         <- cl]) (alCons bitenc clos)
        ]
        where onlyif cond f = if cond then f else const True
              cl = S.toList clos
      --for each check of the checks List, we apply the EncodedAtom to it
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

--consistency Checks functions
--consistency check for T AP
trueCons :: BitEncoding -> EncodedSet -> Bool
trueCons bitenc set = not $ D.member bitenc (Not T) set

--consistency check for (And g h) Formula
andCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
andCons bitenc clos set = not (D.any bitenc consSet set)
                          &&
                          -- if both g and h hold in current atom, then (And g h) must hold as well
                          null [f | f@(And g h) <- S.toList clos,
                                 (D.member bitenc g set) &&
                                 (D.member bitenc h set) &&
                                 not (D.member bitenc f set)]

  where -- if (And g h) holds in current atom, then g and h must both hold as well
        consSet (And g h) = not $ D.member bitenc g set && D.member bitenc h set
        consSet _ = False

--consistency check for (Or g h) Formula
orCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
orCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g or h holds in current atom, then (Or g h) must hold as well
                         null [f | f@(Or g h) <- S.toList clos,
                                ((D.member bitenc g set) ||
                                 (D.member bitenc h set)
                                ) && not (D.member bitenc f set)]

  where -- if (Or g h) holds in current atom, then g or h must hold as well
        consSet (Or g h) = not $ D.member bitenc g set || D.member bitenc h set
        consSet _ = False

-- consistency check for (Xor g h) Formula 
xorCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
xorCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g xor h holds in current atom, then (Xor g h) must hold as well
                         null [f | f@(Xor g h) <- S.toList clos,
                                (xor (D.member bitenc g set) 
                                 (D.member bitenc h set)
                                ) && not (D.member bitenc f set)]                              
  where -- if (Xor g h) holds in current atom, then g xor h must hold as well
        consSet (Xor g h) = not $ xor D.member bitenc g set  D.member bitenc h set
        consSet _ = False

-- consistency check for (Implies g h)
impliesCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
impliesCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g implies h holds in current atom, then (Implies g h) must hold as well
                         null [f | f@(Implies g h) <- S.toList clos,
                                (implies (D.member bitenc g set) 
                                 (D.member bitenc h set)
                                ) && not (D.member bitenc f set)]
  where -- if (Implies g h) holds in current atom, then g implies h must hold as well
        consSet (Implies g h) = not $ implies D.member bitenc g set  D.member bitenc h set
        consSet _ = False

-- consistency check for (Iff g h)
iffCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
iffCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g iff h holds in current atom, then (Iff g h) must hold as well
                         null [f | f@(Iff g h) <- S.toList clos,
                                (iff (D.member bitenc g set) 
                                 (D.member bitenc h set)
                                ) && not (D.member bitenc f set)]
  where -- if (Iff g h) holds in current atom, then g iff h must hold as well
        consSet (Iff g h) = not $ iff D.member bitenc g set  D.member bitenc h set
        consSet _ = False

-- consistency check for (Until dir g h)
untilCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
untilCons bitenc clos set = not (D.any bitenc consSet set)
                            &&
                            -- if h holds or (Until dir g h) still holds in the next (chain) position, then (Until dir g h) must hold in the current atom
                            null [f | f@(Until pset g h) <- S.toList clos,
                                                            present f pset g h &&
                                                            not (D.member bitenc f set)]
  where  -- if (Until dir g h) holds, then it must be that h holds or (Until dir g h) still holds in the next (chain) position
        present u dir g h = D.member bitenc h set
                             || (D.member bitenc g set
                                 && (D.member bitenc (PNext  dir u) set
                                     || D.member bitenc (XNext dir u) set))
        consSet f@(Until dir g h) = not $ present f dir g h
        consSet _ = False

-- consistency check for (Since dir g h)
sinceCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
sinceCons bitenc clos set = not (D.any bitenc consSet set)
                            &&
                            -- if h holds or (Since dir g h) still holds in the previous (chain) position, then (Since dir g h) must hold in the current atom
                            null [f | f@(Since pset g h) <- S.toList clos,
                                                            present f pset g h &&
                                                            not (D.member bitenc f set)]
  where -- if (Since dir g h) holds, then it must be that h holds or (Since dir g h)  holds in the previous (chain) position
        present s dir g h = D.member bitenc h set
                             || (D.member bitenc g set
                                 && (D.member bitenc (PBack dir s) set
                                     || D.member bitenc (XBack dir s) set))
        consSet f@(Since dir g h) = not $ present f dir g h
        consSet _ = False

--TODO update this with POTLv2
-- consistency check for HUntil Up g h
hierUntilUpCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierUntilUpCons bitenc clos set = not (D.any bitenc consSet set)
                                     &&
                                     null [f | f@(HUntil Up g h) <- S.toList clos,
                                                                         present f g h &&
                                                                         not (D.member bitenc f set)]
  where -- if (HUntil Up g h) holds, then or (...) (...) holds
        present huu g h =
          (D.member bitenc h set && D.member bitenc (XBack Down T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HNext Up huu) set)
        consSet f@(HUntil Up g h) = not $ present f g h
        consSet _ = False

-- consistency check for HSince Up g h
hierSinceUpCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierSinceUpCons bitenc clos set = not (D.any bitenc consSet set)
                                     &&
                                     null [f | f@(HSince Up g h) <- S.toList clos,
                                                                         present f g h &&
                                                                         not (D.member bitenc f set)]
  where present hsu g h =
          (D.member bitenc h set && D.member bitenc (XBack Down T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HBack Up hsu) set)
        consSet f@(HSince Up g h) = not $ present f g h
        consSet _ = False

-- consistency check for HUntil Down g h
hierUntilDownCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierUntilDownCons bitenc clos set = not (D.any bitenc consSet set)
                                    &&
                                    null [f | f@(HUntil Down g h) <- S.toList clos,
                                                                       present f g h &&
                                                                       not (D.member bitenc f set)]
  where present hud g h =
          (D.member bitenc h set && D.member bitenc (XNext Up T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HNext Down hud) set)
        consSet f@(HUntil Down g h) = not $ present f g h
        consSet _ = False

-- consistency check for HSince Down g h
hierSinceDownCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierSinceDownCons bitenc clos set = not (D.any bitenc consSet set)
                                    &&
                                    null [f | f@(HSince Down g h) <- S.toList clos,
                                                                       present f g h &&
                                                                       not (D.member bitenc f set)]
  where present hsd g h =
          (D.member bitenc h set && D.member bitenc (XNext Up T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HBack Down hsd) set)
        consSet f@(HSince Down g h) = not $ present f g h
        consSet _ = False

-- consistency check for Eventually g
evCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
evCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         null [f | f@(Eventually' g) <- S.toList clos,
                                                        present f g &&
                                                        not (D.member bitenc f set)]
  where present ev g =
          (D.member bitenc g set) ||
          (D.member bitenc (PNext Up ev) set) ||
          (D.member bitenc (PNext Down ev) set)
        consSet f@(Eventually g) = not $ present f g
        consSet _ = False

-- consistency check for
alCons

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

          pnArgs = V.fromList $ map getPnArg $ filter checkPn (S.toList cl)
          getPnArg f@(PrecNext _ g)
            | negative g = (True, D.singleton bitenc f, D.singleton bitenc (negation g))
            | otherwise  = (False, D.singleton bitenc f, D.singleton bitenc g)

          maskPnp Yield = D.suchThat bitenc (checkPnp Yield)
          maskPnp Equal = D.suchThat bitenc (checkPnp Equal)
          maskPnp Take  = D.suchThat bitenc (checkPnp Take)
          checkPnp prec (PrecNext pset _) = prec `PS.member` pset
          checkPnp _ _ = False

          maskPnnp Yield = D.suchThat bitenc (checkPnnp Yield)
          maskPnnp Equal = D.suchThat bitenc (checkPnnp Equal)
          maskPnnp Take  = D.suchThat bitenc (checkPnnp Take)
          checkPnnp prec (PrecNext pset _) = prec `PS.notMember` pset
          checkPnnp _ _ = False

          precComp prec = D.null $ D.intersect pCurr (maskPnnp prec)

          fsComp prec = pCurrPnfs == checkSet
            where pCurrPnfs = D.intersect pCurr maskPn
                  checkSet = V.foldl' checkSetFold (D.empty bitenc) pnArgs
                  checkSetFold acc (negf, fMask, gMask)
                    | (not . D.null $ D.intersect fMask (maskPnp prec))
                      && ((not negf && (not . D.null $ D.intersect gMask fCurr))
                         || (negf && (D.null $ D.intersect gMask fCurr)))
                    = D.union acc fMask
                    | otherwise = acc

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

          pbArgs = V.fromList $ map getPbArg $ filter checkPb (S.toList cl)
          getPbArg f@(PrecBack _ g)
            | negative g = (True, D.singleton bitenc f, D.singleton bitenc (negation g))
            | otherwise  = (False, D.singleton bitenc f, D.singleton bitenc g)

          maskPbp Yield = D.suchThat bitenc (checkPbp Yield)
          maskPbp Equal = D.suchThat bitenc (checkPbp Equal)
          maskPbp Take  = D.suchThat bitenc (checkPbp Take)
          checkPbp prec (PrecBack pset _) = prec `PS.member` pset
          checkPbp _ _ = False

          maskPbnp Yield = D.suchThat bitenc (checkPbnp Yield)
          maskPbnp Equal = D.suchThat bitenc (checkPbnp Equal)
          maskPbnp Take  = D.suchThat bitenc (checkPbnp Take)
          checkPbnp prec (PrecBack pset _) = prec `PS.notMember` pset
          checkPbnp _ _ = False

          precComp prec = D.null $ D.intersect fCurr (maskPbnp prec)

          fsComp prec = fCurrPbfs == checkSet
            where fCurrPbfs = D.intersect fCurr maskPb
                  checkSet = V.foldl' checkSetFold (D.empty bitenc) pbArgs
                  checkSetFold acc (negf, fMask, gMask)
                    | (not . D.null $ D.intersect fMask (maskPbp prec))
                      && ((not negf && (not . D.null $ D.intersect gMask pCurr))
                         || (negf && (D.null $ D.intersect gMask pCurr)))
                    = D.union acc fMask
                    | otherwise = acc

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
          (fPend, _, _, _) = fprFuturePendComb info

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
      let (_, _, fXe, _) = fprFuturePendComb info
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

delta :: RuleGroup
      -> [Atom]
      -> Set (EncodedSet, Bool, Bool, Bool)
      -> State
      -> Maybe Input
      -> Maybe State
      -> Maybe Input
      -> [State]
delta rgroup atoms pcombs state mprops mpopped mnextprops = fstates
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
isFinal bitenc s =
  debug $ not (mustPush s) -- xe can be instead accepted, as if # = #
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
            (deltaShift as pcs shiftRules)
            (deltaPush  as pcs pushRules)
            (deltaPop   as pcs popRules)
            encTs
  where nphi = normalize . toReducedPotl $ phi
        tsprops = S.toList $ foldl' (S.union) S.empty (sl:ts)
        inputSet = foldl' (flip S.insert) S.empty ts
        encTs = map (D.encodeInput bitenc) ts

        cl = closure nphi tsprops
        bitenc = makeBitEncoding cl
        (prec, sl) = fromStructEnc bitenc sprs
        as = genAtoms bitenc cl inputSet
        pcs = pendCombs bitenc cl
        is = initials nphi cl (as, bitenc)
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec
        debug = id

        deltaShift atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop atoms pcombs rgroup state popped = fstates
          where fstates = delta rgroup atoms pcombs state
                                Nothing (Just popped) Nothing

checkGen :: (Ord a, Show a)
         => Formula a
         -> [StructPrecRel a]
         -> [Set (Prop a)]
         -> Bool
checkGen phi precr ts =
  let (tphi, tprecr, tts) = convPropTokens phi precr ts
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
            (augDeltaShift as pcs shiftRules)
            (augDeltaPush  as pcs pushRules)
            (augDeltaPop   as pcs popRules)
            encTs
  where nphi = normalize . toReducedPotl $ phi

        tsprops = S.toList $ foldl' (S.union) S.empty (sl:ts)
        inputSet = foldl' (flip S.insert) S.empty ts
        encTs = map (D.encodeInput bitenc) ts

        cl = closure nphi tsprops
        bitenc = makeBitEncoding cl
        (prec, sl) = fromStructEnc bitenc sprs
        as = genAtoms bitenc cl inputSet
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

        augDeltaShift atoms pcombs rgroup lookahead state props = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nShift with: " ++ show (S.toList props) ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup atoms pcombs state
                            (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPush atoms pcombs rgroup lookahead state props = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nPush with: " ++ show (S.toList props) ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup atoms pcombs state
                            (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPop atoms pcombs rgroup lookahead state popped = debug fstates
          where
            debug = id
            --debug = DT.trace ("\nPop with popped:\n" ++ show popped ++
            --                  "\nFrom:\n" ++ show state ++ "\nResult:") . DT.traceShowId
            fstates = delta rgroup atoms pcombs state
                            Nothing (Just popped) (Just . laProps $ lookahead)

fastcheckGen :: ( Ord a, Show a)
             => Formula a
             -> [StructPrecRel a]
             -> [Set (Prop a)]
             -> Bool
fastcheckGen phi precr ts =
  let (tphi, tprecr, tts) = convPropTokens phi precr ts
  in fastcheck tphi tprecr tts

--- generate an OPA corresponding to a POTLv2 formula
makeOpa ::  Formula APType -- the input formula
        -> ([Prop APType], [Prop APType]) -- AP (the first list is for structural labels, the second one is for all the propositions of phi)
        -> [StructPrecRel APType]  ---precedence relation array which replaces the usual matrix M
        -> (BitEncoding --the guide for encoding and decoding between bits and formulas and props
           , EncPrecFunc -- operator precedence function??
           , [State] --states 
           , State -> Bool -- isFinal
           , State -> Input -> [State] -- deltaPush
           , State -> Input -> [State] -- deltaShift
           , State -> State -> [State] -- deltaPop
           )
makeOpa phi (sls, als) sprs = (bitenc
                              , prec
                              , is
                              , isFinal bitenc
                              , deltaPush  as pcs pushRules
                              , deltaShift as pcs shiftRules
                              , deltaPop   as pcs popRules
                              )
  where 
        --remove double negations
        nphi = normalize phi
        -- all the atomic propositions (AP) which make up the language (L = powerset(AP))
        -- it contains duplicates
        tsprops = sls ++ als
        --generate the powerset of AP, ech time taking a prop from the structural list
        inputSet = S.fromList [S.fromList (sl:alt) | sl <- sls, alt <- filterM (const [True, False]) als]
        -- generate the closure of the normalized input formulas
        cl = closure nphi tsprops
        -- generate a BitEncoding from the closure
        bitenc = makeBitEncoding cl
        -- generate an EncPrecFunc from a StructPrecRel
        (prec, _) = fromStructEnc bitenc sprs
        --- generate all consistent subsets of cl
        as = genAtoms bitenc cl inputSet
        pcs = pendCombs bitenc cl
        is = initials nphi cl (as, bitenc)
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec

        deltaShift atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPush atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                (Just props) Nothing Nothing

        deltaPop atoms pcombs rgroup state popped = fstates
          where fstates = delta rgroup atoms pcombs state
                                Nothing (Just popped) Nothing





