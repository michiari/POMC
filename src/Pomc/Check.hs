{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Check
   Copyright   : 2020 Davide Bergamaschi, Michele Chiari and Francesco Pontiggia
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Check ( -- * Checking functions
                    check
                  , checkGen
                  , fastcheck
                  , fastcheckGen
                    -- * Checking helpers
                  , closure
                    -- * Printing
                  , showAtom
                  , showState
                  , EncPrecFunc
                  , Input
                  , Atom
                  , State(..)
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.Opa (run, augRun)
import Pomc.Potl (Formula(..), Dir(..), negative, negation, atomic, normalize, future)
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
import Control.Monad (guard, filterM, foldM)
import qualified Data.Sequence as SQ
import Data.Foldable (toList)

import GHC.Generics (Generic)
import Data.Hashable

-- Function that, given two atoms or input symbols,
-- returns the precedence relation between them
type EncPrecFunc = EncodedSet -> EncodedSet -> Maybe Prec

-- generate an EncPrecFunc from a StructPrecRel
fromStructEnc :: BitEncoding -> [StructPrecRel APType] -> (EncPrecFunc, PropSet)
fromStructEnc bitenc sprs = (\s1 s2 -> M.lookup (structLabel s1, structLabel s2) relMap, sl)
  where
        -- a set of all structural labels
        sl = S.fromList $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) sprs
        -- an encoded Atom where all bits corresponding to sl are set
        maskSL = D.inputSuchThat bitenc (flip S.member sl)
        -- a function which makes a bitwise AND between a parameter Atom and the mask
        -- to get only the structural labels out of the parameter Atom
        structLabel s = s `D.intersect` maskSL
        -- map the relation between props into a relation between EncodedAtoms
        relMap = M.fromList $ map (\(sl1, sl2, pr) ->
                                     ((encodeProp sl1, encodeProp sl2), pr)) sprs
        -- encode a single atomic proposition into an EncodedAtom
        encodeProp = D.encodeInput bitenc . S.singleton


type Input = EncodedSet
type Atom = EncodedSet

-- an OPA state
data State = State
    { current   :: Atom -- BitVector representing formulas and AP holding in the present state
    , pending   :: EncodedSet -- BitVector representing temporal obligations holding in the current state
    , mustPush  :: !Bool
    , mustShift :: !Bool
    , afterPop  :: !Bool
    } deriving (Generic, Ord, Eq)

instance Hashable State

-- Begin debugging stuff
showFormulaSet :: (Show a) => (APType -> a) -> FormulaSet -> String
showFormulaSet transAP fset =
  let fs = S.toList fset
      posfs = filter (not . negative) fs
      negfs = filter (negative) fs
  in show $ map (fmap transAP) (posfs ++ negfs)

showAtom :: (Show a) => BitEncoding -> (APType -> a) -> Atom -> String
showAtom bitenc transAP atom =
  "FS: " ++ showFormulaSet transAP (D.decode bitenc atom) ++ "\t\tES: " ++ show atom

instance Show State where
  show (State c p xl xe xr) = "\n{ C: "  ++ show c  ++
                              "\n, P: "  ++ show p  ++
                              "\n, XL: " ++ show xl ++
                              "\n, X=: " ++ show xe ++
                              "\n, XR: " ++ show xr ++
                              "\n}"

showState :: (Show a) => BitEncoding -> (APType -> a) -> State -> String
showState bitenc transAP (State c p xl xe xr) =
  "{ C: "    ++ showAtom bitenc transAP c  ++
  "\n, P: "  ++ showAtom bitenc transAP p  ++
  "\n, XL: " ++ show xl                    ++
  "\n, X=: " ++ show xe                    ++
  "\n, XR: " ++ show xr                    ++
  "\n}"
-- End debugging stuff


-- given a Bit Encoding, a set of all currently holding formulas and AP,
-- and the input APs, determine whether the input APs are satisfied by fset
compProps :: BitEncoding -> EncodedSet -> Input -> Bool
compProps bitenc fset pset = D.extractInput bitenc fset == pset


-- generate a closure (phi = input formula, otherProps = AP set of the language)
closure :: Formula APType -> [Prop APType] -> FormulaSet
closure phi otherProps = let propClos = concatMap (closList . Atomic) (End : otherProps)
                             phiClos  = closList phi
                         in S.fromList (propClos ++ phiClos)
  where
    xbuExpr g = [AuxBack Down g , Not $ AuxBack Down g]
    hndExpr g = [AuxBack Down g , Not (AuxBack Down g) , AuxBack Down (HNext Down g) , Not $ AuxBack Down (HNext Down g)]
    hbdExpr g = [AuxBack Down g , Not (AuxBack Down g) , AuxBack Down (HBack Down g) , Not $ AuxBack Down (HBack Down g)]
    untilExpr dir g h     = [PNext dir (Until dir g h) , XNext dir (Until dir g h) , Not $ PNext dir (Until dir g h) , Not $ XNext dir (Until dir g h)]
    sinceDownExpr g h = [PBack Down (Since Down g h) , XBack Down (Since Down g h) , Not $ PBack Down (Since Down g h) , Not $ XBack Down (Since Down g h)]
    sinceUpExpr g h   = [PBack Up (Since Up g h) , XBack Up (Since Up g h) , Not $ PBack Up (Since Up g h) , Not $ XBack Up (Since Up g h)] ++ xbuExpr (Since Up g h)
    hudExpr g h = [XNext Up T   , Not (XNext Up T)   , T , Not T , HNext Down (HUntil Down g h) , Not $ HNext Down (HUntil Down g h)] ++ hndExpr (HUntil Down g h)
    huuExpr g h = [XBack Down T , Not (XBack Down T) , T , Not T , HNext Up (HUntil Up g h) , Not $ HNext Up (HUntil Up g h)]
    hsdExpr g h = [XNext Up T   , Not (XNext Up T)   , T , Not T , HBack Down (HSince Down g h) , Not $ HBack Down (HSince Down g h)] ++ hbdExpr (HSince Down g h)
    hsuExpr g h = [XBack Down T , Not (XBack Down T) , T , Not T , HBack Up (HSince Up g h) , Not $ HBack Up (HSince Up g h)]
    evExpr    g = [PNext Up (Eventually g), Not $ PNext Up (Eventually g), PNext Down (Eventually g), Not $ PNext Down (Eventually g)]

    closList f =
      case f of
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
        Until dir g h      -> [f, Not f] ++ closList g ++ closList h ++ untilExpr dir g h
        Since Down g h     -> [f, Not f] ++ closList g ++ closList h ++ sinceDownExpr g h
        Since Up g h       -> [f, Not f] ++ closList g ++ closList h ++ sinceUpExpr g h
        HUntil Down g h    -> [f, Not f] ++ closList g ++ closList h ++ hudExpr g h
        HUntil Up g h      -> [f, Not f] ++ closList g ++ closList h ++ huuExpr g h
        HSince Down g h    -> [f, Not f] ++ closList g ++ closList h ++ hsdExpr g h
        HSince Up g h      -> [f, Not f] ++ closList g ++ closList h ++ hsuExpr g h
        Eventually g       -> [f, Not f] ++ closList g ++ evExpr  g
        Always g           -> [f, Not f] ++ closList g
        AuxBack _ g        -> [f, Not f] ++ closList g


-- given a formula closure, generate a bitEncoding
makeBitEncoding :: FormulaSet -> BitEncoding
makeBitEncoding clos =
  let
      -- positive formulas
      pclos = S.filter (not . negative) clos

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
      unwrapProp _ = error "Not a Prop!"

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
      -- each check is partially applied: it still need an encoded atom to run the check on
      checks =
        [ onlyif (T `S.member` clos) (trueCons bitenc)
        , onlyif (not . null $ [f | f@(And _ _)          <- cl]) (andCons bitenc clos)
        , onlyif (not . null $ [f | f@(Or _ _)           <- cl]) (orCons bitenc clos)
        , onlyif (not . null $ [f | f@(Xor _ _)          <- cl]) (xorCons bitenc clos)
        , onlyif (not . null $ [f | f@(Implies _ _)      <- cl]) (impliesCons bitenc clos)
        , onlyif (not . null $ [f | f@(Iff _ _)          <- cl]) (iffCons bitenc clos)
        , onlyif (not . null $ [f | f@(Until _ _ _)      <- cl]) (untilCons bitenc clos)
        , onlyif (not . null $ [f | f@(Since _ _ _)      <- cl]) (sinceCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Down _ _)  <- cl]) (hierUntilDownCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Up _ _)    <- cl]) (hierUntilUpCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Down  _ _) <- cl]) (hierSinceDownCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Up _ _)    <- cl]) (hierSinceUpCons bitenc clos)
        , onlyif (not . null $ [f | f@(Eventually _)     <- cl]) (evCons bitenc clos)
        ]
        where onlyif cond f = if cond then f else const True
              cl = S.toList clos
      -- we apply each check to the EncodedAtom eset
      -- all returns True if all the checks return True
      consistent eset = all (\c -> c eset) checks

      -- Make all consistent atoms
      -- given a starting empty sequence and a BitVector representing a set of formulas,
      -- join it with all the atoms in atomics and check consistency
      prependCons as eset =
        let combs = do easet <- atomics
                       let eset' = D.joinInputFormulas easet eset
                       guard (consistent eset')
                       return eset'
        in as SQ.>< (SQ.fromList combs)

  in toList $ if width bitenc - propBits bitenc == 0
              then SQ.fromList atomics
              else foldl' prependCons SQ.empty (D.generateFormulas bitenc)

-- Consistency check functions

-- consistency check for T
trueCons :: BitEncoding -> EncodedSet -> Bool
trueCons bitenc set = not $ D.member bitenc (Not T) set

-- consistency check for (And g h)
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

-- consistency check for (Or g h)
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

-- consistency check for (Xor g h)
xorCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
xorCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g xor h holds in current atom, then (Xor g h) must hold as well
                         null [f | f@(Xor g h) <- S.toList clos,
                                (xor (D.member bitenc g set)
                                 (D.member bitenc h set))
                                && not (D.member bitenc f set)]
  where -- if (Xor g h) holds in current atom, then g xor h must hold as well
        consSet (Xor g h) = not $ xor (D.member bitenc g set)  (D.member bitenc h set)
        consSet _ = False

-- consistency check for (Implies g h)
impliesCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
impliesCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g implies h holds in current atom, then (Implies g h) must hold as well
                         null [f | f@(Implies g h) <- S.toList clos,
                                (implies (D.member bitenc g set)
                                 (D.member bitenc h set))
                                && not (D.member bitenc f set)]
  where -- if (Implies g h) holds in current atom, then g implies h must hold as well
        consSet (Implies g h) = not $ implies (D.member bitenc g set)  (D.member bitenc h set)
        consSet _ = False

-- consistency check for (Iff g h)
iffCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
iffCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         -- if g iff h holds in current atom, then (Iff g h) must hold as well
                         null [f | f@(Iff g h) <- S.toList clos,
                                (iff (D.member bitenc g set)
                                 (D.member bitenc h set))
                                && not (D.member bitenc f set)]
  where -- if (Iff g h) holds in current atom, then g iff h must hold as well
        consSet (Iff g h) = not $ iff (D.member bitenc g set) ( D.member bitenc h set)
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
                            -- if h holds or (Since dir g h) still holds in the previous (chain) position,
                            -- then (Since dir g h) must hold in the current atom
                            null [f | f@(Since pset g h) <- S.toList clos,
                                   present f pset g h &&
                                   not (D.member bitenc f set)]
  where -- if (Since dir g h) holds, then h holds or (Since dir g h)
        -- holds in the previous (chain) position
        present s dir g h = D.member bitenc h set
                             || (D.member bitenc g set
                                 && (D.member bitenc (PBack dir s) set
                                     || D.member bitenc (XBack dir s) set))
        consSet f@(Since dir g h) = not $ present f dir g h
        consSet _ = False

-- consistency check for (HUntil Down g h)
hierUntilDownCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
hierUntilDownCons bitenc clos set = not (D.any bitenc consSet set)
                                     &&
                                     null [f | f@(HUntil Down g h) <- S.toList clos,
                                            present f g h &&
                                            not (D.member bitenc f set)]
  where -- if (HUntil Down g h) holds, then or (...) (...) holds
        present hud g h =
          (D.member bitenc h set && D.member bitenc (XNext Up T) set)
          ||
          (D.member bitenc g set && D.member bitenc (HNext Down hud) set)
        consSet f@(HUntil Down g h) = not $ present f g h
        consSet _ = False


-- consistency check for (HUntil Up g h)
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

-- consistency check for (HSince Down g h)
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


-- consistency check for (HSince Up g h)
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

-- consistency check for (Eventually g)
evCons :: BitEncoding -> FormulaSet -> EncodedSet -> Bool
evCons bitenc clos set = not (D.any bitenc consSet set)
                         &&
                         null [f | f@(Eventually g) <- S.toList clos,
                                present f g &&
                                not (D.member bitenc f set)]
  where present ev g =
          (D.member bitenc g set) ||
          (D.member bitenc (PNext Up ev) set) ||
          (D.member bitenc (PNext Down ev) set)
        consSet f@(Eventually g) = not $ present f g
        consSet _ = False

-- given the BitEncoding and the closure of phi,
-- generate all possible combinations of pending obligations + (mustPush, mustShift, afterPop)
pendCombs :: BitEncoding -> FormulaSet -> Set (EncodedSet, Bool, Bool, Bool)
pendCombs bitenc clos =
  let xnMasks = [D.singleton bitenc f | f@(XNext _ _)   <- S.toList clos]
      xbMasks = [D.singleton bitenc f | f@(XBack _ _)   <- S.toList clos]
      hnMasks = [D.singleton bitenc f | f@(HNext _ _)   <- S.toList clos]
      hbMasks = [D.singleton bitenc f | f@(HBack _ _)   <- S.toList clos]
      axbMasks = [D.singleton bitenc f | f@(AuxBack _ _) <- S.toList clos]
      pendSets = foldM (\set mask -> [set, set `D.union` mask]) (D.empty bitenc)
                 (xnMasks ++ xbMasks ++ hnMasks ++ hbMasks ++ axbMasks)
      combs pset = S.fromList [(pset, xl, xe, xr) | xl <- [False, True]
                                                  , xe <- [False, True]
                                                  , xr <- [False, True]
                                                  , not (xl && xe)]
  in foldl' S.union S.empty $ map combs pendSets

-- given phi, the closure of phi, the set of consistent atoms and the bitencoding, generate all the initial states
initials :: Formula APType -> FormulaSet -> ([Atom], BitEncoding) -> [State]
initials phi clos (atoms, bitenc) =
  let compatible atom = let set = atom
                            checkPb (PBack {}) = True
                            checkPb _ = False
                            checkAuxB (AuxBack Down _) = True
                            checkAuxB _ = False
                            checkxb (XBack _ _) = True
                            checkxb _ = False
                        in D.member bitenc phi set && -- phi must be satisfied in the initial state
                           (not $ D.any bitenc checkPb set) && -- the initial state must have no PBack
                           (not $ D.any bitenc checkAuxB set) && -- the initial state must have no AuxBack
                           (not $ D.any bitenc checkxb set)  -- the initial state must have no XBack
      compAtoms = filter compatible atoms
      xndfSet = S.fromList  [f | f@(XNext Down _) <- S.toList clos]
  -- list comprehension with all the states that are compatible and the powerset of all possible future obligations
  in [State phia (D.encode bitenc phip) True False False | phia <- compAtoms,
                                                           phip <- S.toList (S.powerSet xndfSet)]

-- return all deltaRules b satisfying condition (i -> Bool) on i (a closure)
resolve :: i -> [(i -> Bool, b)] -> [b]
resolve info conditionals = snd . unzip $ filter (\(cond, _) -> cond info) conditionals

-- given a BitEncoding, the closure of phi, and the precedence function, generate all Rule groups: (shift rules, push rules, pop rules)
deltaRules :: BitEncoding -> FormulaSet -> EncPrecFunc -> (RuleGroup, RuleGroup, RuleGroup)
deltaRules bitenc cl precFunc =
  let
      -- SHIFT RULES
      shiftGroup = RuleGroup
        {
          -- present rules
          ruleGroupPrs  = resolve cl [ (const True, xlShiftPr)
                                     , (const True, xeShiftPr)
                                     , (const True, propShiftPr)
                                     , (xndCond,    xndShiftPr)
                                     , (xnuCond,    xnuShiftPr)
                                     , (xbdCond,    xbdShiftPr)
                                     , (xbuCond,    xbuShiftPr)
                                     , (abdCond,    abdShiftPr)
                                     , (hnuCond,    hnuShiftPr)
                                     , (hbuCond,    hbuShiftPr)
                                     , (hbdCond,    hbdShiftPr)
                                     , (alwCond,    alwShiftPr)
                                     ]
        , ruleGroupFcrs = resolve cl [ (alwCond, alwShiftFcr) ]
        , ruleGroupFprs = resolve cl [ (const True, xrShiftFpr)
                                     , (xndCond,    xndShiftFpr)
                                     , (xnuCond,    xnuShiftFpr)
                                     , (xbdCond,    xbdShiftFpr)
                                     , (xbuCond,    xbuShiftFpr)
                                     , (abdCond,    abdShiftFpr)
                                     , (hndCond,    hndShiftFpr1)
                                     , (hndCond,    hndShiftFpr2)
                                     , (hbdCond,    hbdShiftFpr)
                                     ]
        , ruleGroupFrs  = resolve cl [ (const True, xlXeShiftFr)
                                     , (pnCond,     pnShiftFr)
                                     , (pbCond,     pbShiftFr)
                                     ]
        }
      -- PUSH RULES
      pushGroup = RuleGroup
        {
          -- present rules
          ruleGroupPrs  = resolve cl [ (const True, xlPushPr)
                                     , (const True, xePushPr)
                                     , (const True, propPushPr)
                                     , (xbdCond,    xbdPushPr)
                                     , (xbuCond,    xbuPushPr)
                                     , (abdCond,    abdPushPr)
                                     , (hnuCond,    hnuPushPr1)
                                     , (hnuCond,    hnuPushPr2)
                                     , (hbuCond,    hbuPushPr)
                                     , (hbdCond,    hbdPushPr)
                                     , (alwCond,    alwPushPr)
                                     ]
        , ruleGroupFcrs = resolve cl [ (alwCond, alwPushFcr) ]
        , ruleGroupFprs = resolve cl [ (const True, xrPushFpr)
                                     , (xndCond,    xndPushFpr)
                                     , (xnuCond,    xnuPushFpr)
                                     , (xbdCond,    xbdPushFpr)
                                     , (xbuCond,    xbuPushFpr)
                                     , (abdCond,    abdPushFpr)
                                     , (hndCond,    hndPushFpr1)
                                     , (hndCond,    hndPushFpr2)
                                     , (hbdCond,    hbdPushFpr)
                                     ]
        , ruleGroupFrs  = resolve cl [ (const True, xlXePushFr)
                                     , (pnCond,     pnPushFr)
                                     , (pbCond,     pbPushFr)
                                     ]
        }
      -- POP RULES
      popGroup = RuleGroup
        {
          -- present rules
          ruleGroupPrs  = resolve cl [ (const True, xlPopPr)
                                     , (const True, xePopPr)
                                     , (xndCond,    xndPopPr)
                                     , (xnuCond,    xnuPopPr)
                                     , (hnuCond,    hnuPopPr)
                                     ]
        ,
          -- future current rules
          ruleGroupFcrs = resolve cl [ (alwCond, alwPopFcr) ]

        , ruleGroupFprs = resolve cl [ (const True, xrPopFpr)
                                     , (xndCond,    xndPopFpr)
                                     , (xnuCond,    xnuPopFpr)
                                     , (xbdCond,    xbdPopFpr)
                                     , (xbuCond,    xbuPopFpr)
                                     , (abdCond,    abdPopFpr)
                                     , (hnuCond,    hnuPopFpr)
                                     , (hndCond,    hndPopFpr1)
                                     , (hndCond,    hndPopFpr2)
                                     , (hndCond,    hndPopFpr3)
                                     , (hbdCond,    hbdPopFpr1)
                                     , (hbdCond,    hbdPopFpr2)
                                     , (hbdCond,    hbdPopFpr3)
                                     ]
        , ruleGroupFrs  = resolve cl [ (hbuCond, hbuPopFr) ]
        }
  in (shiftGroup, pushGroup, popGroup)
  where
    -- XL rules :: PrInfo -> Bool
    xlShiftPr info = let pXl = mustPush (prState info) in not pXl
    xlPushPr  info = let pXl = mustPush (prState info) in pXl
    xlPopPr   info = let pXl = mustPush (prState info) in not pXl
    --

    -- XE rules :: PrInfo -> Bool
    xeShiftPr info = let pXe = mustShift (prState info) in pXe
    xePushPr  info = let pXe = mustShift (prState info) in not pXe
    xePopPr   info = let pXe = mustShift (prState info) in not pXe
    --

    xlXePushFr :: FrInfo -> Bool
    xlXePushFr info =
      let pCurr = current $ frState info -- set of formulas that hold in current position
          fCurr = frFutureCurr info -- future current holding formulas
          (_, fXl, fXe, _) = frFuturePendComb info
          -- since the symbol read by a push or a shift gets on top of the stack,
          -- the next move is determined by the precedence relation between it and the next input
      in case precFunc pCurr fCurr of
        Just Yield -> fXl
        Just Equal -> fXe
        Just Take -> not (fXe || fXl)
        Nothing -> False

    xlXeShiftFr :: FrInfo -> Bool
    xlXeShiftFr = xlXePushFr

    -- XR rules ::  FprInfo -> Bool
    xrShiftFpr info = let (_, _, _, fXr) = fprFuturePendComb info in not fXr
    xrPushFpr  info = let (_, _, _, fXr) = fprFuturePendComb info in not fXr
    xrPopFpr   info = let (_, _, _, fXr) = fprFuturePendComb info in fXr
    --

    propPushPr :: PrInfo -> Bool
    propPushPr info =
      case prProps info of
        Nothing -> True -- we trust that we have been given the right input symbol
        Just props -> compProps bitenc (current . prState $ info) props
        -- otherwise we check that the input AP are the same as in the current state

    propShiftPr :: PrInfo -> Bool
    propShiftPr = propPushPr


    -- PN rules --
    pnCond :: FormulaSet -> Bool
    pnCond clos = not (null [f | f@(PNext _ _) <- S.toList clos])

    pnPushFr :: FrInfo -> Bool
    pnPushFr info =
      let pCurr = current $ frState info -- set of formulas that hold in current position
          fCurr = frFutureCurr info -- future current holding formulas
          (_, fXl, fXe, _) = frFuturePendComb info

          -- BitVector where all ones correspond to PNext operators
          maskPn = D.suchThat bitenc checkPn
          checkPn (PNext _ _) = True
          checkPn _ = False

          -- a tuple made of all arguments of PNext formulas in the closure
          pndArgs = V.fromList $ foldl' (getPnDirArg Down) [] (S.toList cl) -- get all the arguments of PNext Down operators
          pnuArgs = V.fromList $ foldl' (getPnDirArg Up) [] (S.toList cl) -- get all the arguments of PNext Up operators
          pnArgs = pndArgs V.++ pnuArgs -- get all the arguments of PNext operators

          getPnDirArg dir rest f@(PNext thisDir g)
            | dir /= thisDir = rest
            | negative g = (True, D.singleton bitenc f, D.singleton bitenc (negation g)) : rest -- negative arguments are put in positive form
            | otherwise  = (False, D.singleton bitenc f, D.singleton bitenc g) : rest
          getPnDirArg _ rest _ = rest

          -- choosePnArgs fXl fXe
          choosePnArgs _ True = pnArgs -- if next move is a shift, any PNext can hold
          choosePnArgs True _ = pndArgs -- if next move is a push, only PNext Down can hold
          choosePnArgs _ _ = pnuArgs -- if next move is a pop, only PNext Up can hold

          pCurrPnfs = D.intersect pCurr maskPn -- current holding PNext formulas
          checkSet = V.foldl' checkSetFold (D.empty bitenc) (choosePnArgs fXl fXe) -- PNext formulas that should currently hold according to future formulas
          checkSetFold acc (negf, fMask, gMask)
            | ((not negf && (not . D.null $ D.intersect gMask fCurr)) -- a positive PNext and the formula g holds in the next state
                || (negf && (D.null $ D.intersect gMask fCurr))) -- or a negative PNext and the formula g does not hold in the next state
            = D.union acc fMask
            | otherwise = acc

      in pCurrPnfs == checkSet -- if PNext g holds in the current state, then g must hold in the next state, and viceversa

    pnShiftFr :: FrInfo -> Bool
    pnShiftFr = pnPushFr
    --

    -- PB rules --
    pbCond :: FormulaSet -> Bool
    pbCond clos = not (null [f | f@(PBack _ _) <- S.toList clos])

    pbPushFr :: FrInfo -> Bool
    pbPushFr info =
      let pCurr = current $ frState info -- BitVector of formulas holding in current position
          fCurr = frFutureCurr info -- future current holding formulas
          (_, fXl, fXe, _) = frFuturePendComb info

          -- a BitVector where all ones correspond to PBack operators
          maskPb = D.suchThat bitenc checkPb
          checkPb (PBack _ _) = True
          checkPb _ = False

          -- a tuple made of all arguments of PBack formulas in the closure
          pbdArgs = V.fromList $ foldl' (getPbDirArg Down) [] (S.toList cl) -- get all the arguments of PBack Down operators
          pbuArgs = V.fromList $ foldl' (getPbDirArg Up) [] (S.toList cl) -- get all the arguments of PBack Up operators
          pbArgs = pbdArgs V.++ pbuArgs -- get all the arguments of PBack operators

          getPbDirArg dir rest f@(PBack thisDir g)
            | dir /= thisDir = rest
            | negative g = (True, D.singleton bitenc f, D.singleton bitenc (negation g)) : rest -- negative arguments are put in positive form
            | otherwise  = (False, D.singleton bitenc f, D.singleton bitenc g) : rest
          getPbDirArg _ rest _ = rest

          -- choosePbArgs fXl fXe
          choosePbArgs _ True = pbArgs -- if next move is a shift, any PBack can hold
          choosePbArgs True _ = pbdArgs -- if next move is a push, only PBack Down can hold
          choosePbArgs _ _ = pbuArgs -- if next move is a pop, only PBack Up can hold

          fCurrPbfs = D.intersect fCurr maskPb -- PBack formulas holding in the next state
          checkSet = V.foldl' checkSetFold (D.empty bitenc) (choosePbArgs fXl fXe) -- future PBack formulas according to present formulas
          checkSetFold acc (negf, fMask, gMask)
            | ((not negf && (not . D.null $ D.intersect gMask pCurr)) -- a positive PBack and the formula g holds in the next state
                || (negf && (D.null $ D.intersect gMask pCurr))) -- or a negative PBack and the formula g does not hold in the next state
            = D.union acc fMask
            | otherwise = acc

      in fCurrPbfs == checkSet -- if PBack g holds in the current state, then g must hold in the next state, and viceversa

    pbShiftFr = pbPushFr

    -- XND: XNext Down --
    -- get a mask with all XNext Down formulas set to one
    maskXnd = D.suchThat bitenc checkXnd
    checkXnd (XNext Down _) = True
    checkXnd _ = False

    -- check whether we have some XNext Down in the closure
    xndCond :: FormulaSet -> Bool
    xndCond clos = not (null [f | f@(XNext Down _) <- S.toList clos])

    xndPushFpr :: FprInfo -> Bool
    xndPushFpr info =
      let pCurr = current $ fprState info -- current holding propositions
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          pCurrXndfs = D.intersect pCurr maskXnd -- current holding XNext Down formulas
          fPendXndfs = D.intersect fPend maskXnd -- future pending XNext Down obligations

      in if fXl -- if  nextState mustPush
           then pCurrXndfs == fPendXndfs
           else D.null pCurrXndfs -- if not mustPush, then here mustn't be XNext Down formulas

    xndShiftFpr = xndPushFpr

    xndPopFpr :: FprInfo -> Bool
    xndPopFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          ppPendXndfs = D.intersect maskXnd ppPend -- all XNext Down pending obligations of state to pop

          xndClos = S.filter checkXnd cl -- get all XNext Down formulas of the closure
          pCheckSet = D.encode bitenc $
                      S.filter (\(XNext _ g) -> D.member bitenc g pCurr) xndClos -- get all (XNext Down g) formulas of the closure such that g currently holds

          fCheckSet = D.intersect fPend maskXnd -- future XNext Down pending obligations

          checkSet = D.union pCheckSet fCheckSet -- or (future XNext Down pending obligation) (XNext Down g such that g currently hold)

      in  if fXl -- if next state mustPush
            then ppPendXndfs == checkSet -- all XNext Down pending obligations of state to pop are valid if or ...
            else ppPendXndfs == fCheckSet -- all XNext Down pending obligations of state to pop are valid if they hold as pending obligations in the next state

    xndPopPr :: PrInfo -> Bool
    xndPopPr info =
      let pPend = pending $ prState info -- current pending obligations
          pPendXndfs = D.intersect pPend maskXnd --current pending XNext Down obligations
      in  D.null pPendXndfs -- no pending XNext Down is allowed in current state when popping

    xndShiftPr :: PrInfo -> Bool
    xndShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending obligations
          pPendXndfs = D.intersect pPend maskXnd -- current pending XNext Down obligations

          xndClos = S.filter checkXnd cl -- get all XNext Down formulas
          pCheckList = D.encode bitenc $ -- get all (XNext Down g) formulas of the closure such that g currently holds
                       S.filter (\(XNext _ g) -> D.member bitenc g pCurr) xndClos

      in pCheckList == pPendXndfs -- XNext Down g is a current pending obligation iff g holds in the current state


    -- XNU: XNext Up --
    -- get a mask with all XNext Up formulas set to one
    maskXnu = D.suchThat bitenc checkXnu
    checkXnu (XNext Up _) = True
    checkXnu _ = False

    -- check whether we have some XNext Up in the closure
    xnuCond :: FormulaSet -> Bool
    xnuCond clos = not (null [f | f@(XNext Up _) <- S.toList clos])

    xnuPushFpr :: FprInfo -> Bool
    xnuPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXnufs = D.intersect fPend maskXnu -- future pending XNext Up obligations
          pCurrXnufs = D.intersect pCurr maskXnu -- current holding XNext Up formulas
      in if fXl -- if next state must push
           then pCurrXnufs == fPendXnufs
           else D.null pCurrXnufs -- if not mustPush, then here mustn't be XNext Down formulas

    xnuShiftFpr :: FprInfo -> Bool
    xnuShiftFpr = xnuPushFpr

    xnuPopPr :: PrInfo -> Bool
    xnuPopPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending (prState info) --current pending obligations
          pPendXnufs = D.intersect pPend maskXnu -- current pending XNext Up obligations

          xnuClos = S.filter checkXnu cl -- all XNext Up formulas in the closure
          pCheckList = D.encode bitenc $
                       S.filter (\(XNext _ g) -> D.member bitenc g pCurr) xnuClos -- all (XNext Up g) such that g currently holds

      in pCheckList == pPendXnufs

    xnuPopFpr :: FprInfo -> Bool
    xnuPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendXnufs = D.intersect ppPend maskXnu -- XNext Up pending obligations of state to pop
          fPendXnufs = D.intersect fPend maskXnu -- XNext Up future pending obligations
      in ppPendXnufs == fPendXnufs

    xnuShiftPr :: PrInfo -> Bool
    xnuShiftPr = xnuPopPr

    -----------------------------------------------------------------------------
    -- XBD: XBack Down
    -- get a mask with all XBack Down set to one
    maskXbd = D.suchThat bitenc checkXbd
    checkXbd (XBack Down _) = True
    checkXbd _ = False

    xbdCond :: FormulaSet -> Bool
    xbdCond clos = not (null [f | f@(XBack Down _) <- S.toList clos])

    xbdPushPr :: PrInfo -> Bool
    xbdPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending obligations
          pXr = afterPop (prState info) -- was the previous transition a pop?
          pCurrXbdfs = D.intersect pCurr maskXbd -- current holding XBack Down formulas
          pPendXbdfs = D.intersect pPend maskXbd -- current pending XBack Down formulas
      in if pXr
         then pCurrXbdfs == pPendXbdfs
         else D.null pCurrXbdfs

    xbdShiftPr :: PrInfo -> Bool
    xbdShiftPr = xbdPushPr

    xbdPopFpr :: FprInfo -> Bool
    xbdPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendXbdfs = D.intersect ppPend maskXbd -- XBack Down pending obligations of state to pop
          fPendXbdfs = D.intersect fPend maskXbd -- XBack Down future pending obligations
      in ppPendXbdfs == fPendXbdfs

    xbdPushFpr :: FprInfo -> Bool
    xbdPushFpr info =
      let pCurr = current $ fprState info --current holding formulas
          (fPend, _, _, _) = fprFuturePendComb info -- future pending formulas
          fPendXbdfs = D.intersect fPend maskXbd -- future pending XBack Down formulas
          xbdClos = S.filter checkXbd cl -- all XBack Down formulas in the closure
          pCheckSet = D.encode bitenc $
                      S.filter (\(XBack _ g) -> D.member bitenc g pCurr) xbdClos -- all (XBack Down g) such that g currently holds
      in fPendXbdfs == pCheckSet

    xbdShiftFpr :: FprInfo -> Bool
    xbdShiftFpr = xbdPushFpr

    -----------------------------------------------------------------------------
    -- XBU: XBack Up --
    -- a mask with all XBack Up formulas set to True
    maskXbu = D.suchThat bitenc checkXbu
    checkXbu (XBack Up _) = True
    checkXbu _ = False

    -- checking whether there are XBack Up formulas in the closure
    xbuCond :: FormulaSet -> Bool
    xbuCond clos = not (null [f | f@(XBack Up _) <- S.toList clos])

    xbuPushFpr :: FprInfo -> Bool
    xbuPushFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXbufs = D.intersect fPend maskXbu
      in D.null fPendXbufs

    xbuShiftFpr :: FprInfo -> Bool
    xbuShiftFpr = xbuPushFpr

    xbuPushPr :: PrInfo -> Bool
    xbuPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pXr = afterPop $ prState info  -- was the previous transition a pop?
          pCurrXbufs = D.intersect pCurr maskXbu -- current holding XBack Up formulas
          pPendXbufs = D.intersect pPend maskXbu -- current pending XBack Up formulas
      in if pXr
           then pCurrXbufs == pPendXbufs
           else D.null pCurrXbufs

    xbuShiftPr :: PrInfo -> Bool
    xbuShiftPr = xbuPushPr

    xbuPopFpr :: FprInfo -> Bool
    xbuPopFpr info =
      let pPend = pending (fprState info) -- current pending obligations
          pPendXbufs = D.intersect pPend maskXbu -- current XBack Up pending obligations
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXbufs = D.intersect fPend maskXbu -- future XBack Up pending obligations

          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in the state to pop
          xbuClos = S.filter checkXbu cl -- get all XBack Up formulas of the closure
          ppCheckSet = D.encode bitenc $
                      S.filter (\(XBack Up g) -> D.member bitenc (AuxBack Down g) ppCurr) xbuClos
                      -- get all (XBack Up g) such that (AuxBack Down g) currently holds in state to pop
          checkSet = D.union ppCheckSet  pPendXbufs
      in if fXl
         then  pPendXbufs == fPendXbufs
         else  fPendXbufs == checkSet

    -----------------------------------------------------------------------------
    -- ABD: AuxBack Down --
    maskAbd = D.suchThat bitenc checkAbd
    checkAbd (AuxBack Down _) = True
    checkAbd _ = False

    abdCond :: FormulaSet -> Bool
    abdCond clos = not (null [f | f@(AuxBack Down _) <- S.toList clos])

    abdPushPr :: PrInfo -> Bool
    abdPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pCurrAbdfs = D.intersect pCurr maskAbd -- currently holding AuxBack Down formulas
          pPendAbdfs = D.intersect pPend maskAbd -- currently pending AuxBack Down formulas
      in
        pCurrAbdfs == pPendAbdfs

    abdShiftPr :: PrInfo -> Bool
    abdShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
      in D.null $ D.intersect pCurr maskAbd -- no AuxBack Down formulas are allowed when shifting

    abdPopFpr :: FprInfo -> Bool
    abdPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending formulas of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendAbdfs = D.intersect ppPend maskAbd -- pending AuxBack Down formulas of state to pop
          fPendAbdfs = D.intersect fPend maskAbd -- future pending AuxBack Down formulas
      in ppPendAbdfs == fPendAbdfs

    abdPushFpr :: FprInfo -> Bool
    abdPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, _, _, _) = fprFuturePendComb info -- future pending formulas
          fPendAbdfs = D.intersect fPend maskAbd -- future pending AuxBack Down formulas

          abdClos = S.filter checkAbd cl -- get all AuxBack Down formulas of the closure
          pCheckSet = D.encode bitenc $
                      S.filter (\(AuxBack _ g) -> D.member bitenc g pCurr) abdClos
                      -- get all (AuxBack Down g) such that g currently holds

      in fPendAbdfs == pCheckSet

    abdShiftFpr :: FprInfo -> Bool
    abdShiftFpr = abdPushFpr

    -----------------------------------------------------------------------------
    -- HNU: HNext Up --
    -- a mask with all HNext Up formulas set to one
    maskHnu = D.suchThat bitenc checkHnu
    checkHnu (HNext Up _) = True
    checkHnu _ = False

    hnuCond :: FormulaSet -> Bool
    hnuCond clos = not (null [f | f@(HNext Up _) <- S.toList clos])

    hnuPushPr1 :: PrInfo -> Bool
    hnuPushPr1 info =
      let pCurr = current $ prState info -- current holding formulas
          pCurrHnufs = D.intersect pCurr maskHnu -- current holding HNext Up formulas
          pXr = afterPop (prState info) -- was the last transition a pop?
      in if not $ D.null pCurrHnufs
           then pXr
           else True

    hnuPushPr2 :: PrInfo -> Bool
    hnuPushPr2 info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pXr = afterPop $ prState info -- was the last transition a pop?
          pPendHnufs = D.intersect pPend maskHnu -- current pending HNext Up formulas

          hnuClos = S.filter checkHnu cl -- all HNext Up formulas in the closure
          checkSet = D.encode bitenc $
                     S.filter (\(HNext _ g) -> D.member bitenc g pCurr) hnuClos -- all (HNext Up g) such that g currently holds
      in if pXr
           then pPendHnufs == checkSet
           else D.null pPendHnufs

    hnuPopFpr :: FprInfo -> Bool
    hnuPopFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- formulas currently holding in state to pop
          ppXr = afterPop $ fromJust (fprPopped info) -- did the state to pop came from a pop transition?
          fPendHnufs = D.intersect fPend maskHnu -- all future pending HNext Up formulas
          ppCurrHnufs = D.intersect ppCurr maskHnu -- HNext Up formulas holding in state to pop
      in if ppXr
         then ppCurrHnufs == fPendHnufs
        else True

    hnuPopPr :: PrInfo -> Bool
    hnuPopPr info =
      let pPend = pending (prState info) -- current pending obligations
          pPendHnufs = D.intersect pPend maskHnu -- current HNext Up pending obligations
      in D.null pPendHnufs -- no HNext Up obligations are allowed when popping

    hnuShiftPr :: PrInfo -> Bool
    hnuShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formuals
          pCurrHnufs = D.intersect pCurr maskHnu -- current HNext Up holding formulas
          pPendHnufs = D.intersect pPend maskHnu -- current HNext Up pending formuals
      in D.null pCurrHnufs && D.null pPendHnufs -- no pending or holding HNext Up formulas are allowed when shifting

    -----------------------------------------------------------------------------
    -- HBU: HBack Up --
    -- a mask with all XBack Up formulas set to one
    maskHbu = D.suchThat bitenc checkHbu
    checkHbu (HBack Up _) = True
    checkHbu _ = False

    hbuCond :: FormulaSet -> Bool
    hbuCond clos = not (null [f | f@(HBack Up _) <- S.toList clos])

    hbuPushPr :: PrInfo -> Bool
    hbuPushPr info =
      let pCurr = current $ prState info --current holding formulas
          pXl = mustPush $ prState info -- mustPush?
          pXr = afterPop $ prState info -- was the last transition a pop?
          pCurrHbufs = D.intersect pCurr maskHbu --currently holding HBack Up formulas

      in if not $ D.null $ pCurrHbufs
         then pXl && pXr
         else True

    hbuPopFr ::  FrInfo -> Bool
    hbuPopFr info =
      let (_, fXl, _, _) = frFuturePendComb info -- future pending obligations
          fCurr = frFutureCurr info -- future current holding formulas
          ppCurr = current $ fromJust (frPopped info) -- holding formulas in state to pop
          ppXr = afterPop $ fromJust (frPopped info) -- did the state to pop come from a pop?
          fCurrHbufs = D.intersect fCurr maskHbu -- future current holding XBack Up formulas

          hbuClos = S.filter checkHbu cl -- HBack Up formulas in the closure
          checkSet = D.encode bitenc $
                     S.filter (\(HBack Up g) -> D.member bitenc g ppCurr) hbuClos -- all (HBack Up g) such that g holds in state to pop
      in if fXl
         then (if ppXr
              then fCurrHbufs == checkSet
              else D.null fCurrHbufs)
         else True

    hbuShiftPr :: PrInfo -> Bool
    hbuShiftPr info =
      let pCurr = current $ prState info --current holding states
          pCurrHbufs = D.intersect pCurr maskHbu -- currently holding HBack Up formulas
      in D.null  $ pCurrHbufs -- no holding HBack Up is allowed when shifting

    --
    -- HND: HNext Down
    -- a mask with all HNext Down formulas set to one
    maskHnd = D.suchThat bitenc checkHnd
    checkHnd (HNext Down _) = True
    checkHnd _ = False
    hndClos = S.filter checkHnd cl -- all HNext Down formulas in the closure

    hndCond :: FormulaSet -> Bool
    hndCond clos = not (null [f | f@(HNext Down _) <- S.toList clos])

    hndPopFpr1 :: FprInfo -> Bool
    hndPopFpr1 info =
      let (fPend, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          fPendHndfs = D.intersect fPend maskHnd -- future pending HNext Down obligations

          checkSet = D.encode bitenc $
                     S.filter (\(HNext _ g) -> D.member bitenc (AuxBack Down g) ppCurr) hndClos
                     -- all (HNext Down g) formulas such that AuxBack Down g holds in state to pop

      in if not fXl && not fXe
           then fPendHndfs == checkSet
           else True

    hndPopFpr2 :: FprInfo -> Bool
    hndPopFpr2 info =
      let pPend = pending (fprState info) -- current pending obligations
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- current holding formulas in state to pop

          pPendHndfs = D.intersect pPend maskHnd  -- current pending HNext Down formulas

          checkSet = D.encode bitenc $
                     S.filter (\f -> D.member bitenc (AuxBack Down f) ppCurr) hndClos
                     -- all HNext Down g such that AuxBack Down HNext Down g holds in state to pop

      in if not fXl && not fXe
          then pPendHndfs == checkSet
         else True

    hndPopFpr3 :: FprInfo -> Bool
    hndPopFpr3 info =
      let (_, _, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- current holding formulas in state to pop
          checkSet = S.filter (\f -> D.member bitenc (AuxBack Down f) ppCurr) hndClos
          -- all HNext Down g formulas such that AuxBack Down HNext Down  g holds in state to pop

      in if not (null checkSet)
           then not fXe
           else True

    hndPushFpr1 :: FprInfo -> Bool
    hndPushFpr1 info =
      let pCurr = current $ fprState info -- current holding formulas
          (_, fXl, _, _) = fprFuturePendComb info -- future pending obligations
      in if not $ D.null $ D.intersect pCurr maskHnd
         then fXl
         else True

    hndShiftFpr1 :: FprInfo -> Bool
    hndShiftFpr1 = hndPushFpr1

    hndPushFpr2 :: FprInfo -> Bool
    hndPushFpr2 info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          fPendHndfs = D.intersect fPend maskHnd -- future pending HNext Down obligations
      in D.null fPendHndfs

    hndShiftFpr2 :: FprInfo -> Bool
    hndShiftFpr2 = hndPushFpr2
    --

    -- HBD: HBack Down
    -- a mask with all HBack Down formulas set to one
    maskHbd = D.suchThat bitenc checkHbd
    checkHbd (HBack Down _) = True
    checkHbd _ = False
    hbdClos = S.filter checkHbd cl -- all HBack Down formulas in the closure

    hbdCond :: FormulaSet -> Bool
    hbdCond clos = not (null [f | f@(HBack Down _) <- S.toList clos])

    hbdPopFpr1 :: FprInfo -> Bool
    hbdPopFpr1 info =
      let pPend = pending (fprState info) -- current pending formulas
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          pPendHbdfs = D.intersect pPend maskHbd -- current pending HBack Down formulas

          checkSet = D.encode bitenc $
                     S.filter (\(HBack _ g) -> D.member bitenc (AuxBack Down g) ppCurr) hbdClos
                     -- all (HBack Down g) formulas such that (AuxBack Down g) holds in state to pop

      in if not fXl && not fXe
           then pPendHbdfs == checkSet
           else True

    hbdPopFpr2 :: FprInfo -> Bool
    hbdPopFpr2 info =
      let (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          fPendHbdfs = D.intersect fPend maskHbd -- future pending HBack Down formulas


          checkSet = D.encode bitenc $
                     S.filter (\f -> D.member bitenc (AuxBack Down f) ppCurr) hbdClos
                     -- all (HBack Down g) formulas such that (AuxBack Down (HBack Down g)) holds in state to pop

      in if not fXl
           then fPendHbdfs == checkSet
           else True

    hbdPopFpr3 :: FprInfo -> Bool
    hbdPopFpr3 info =
      let pPend = pending (fprState info) -- current pending formulas
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          pPendHbdfs = D.intersect pPend maskHbd -- current pending HBack Down formulas
      in if not (D.null pPendHbdfs)
           then not fXl && not fXe
           else True

    hbdPushFpr :: FprInfo -> Bool
    hbdPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (_, fXl, _, _) = fprFuturePendComb info -- future pending obligations
      in if not $ D.null $ D.intersect pCurr maskHbd
         then fXl
         else True

    hbdShiftFpr :: FprInfo -> Bool
    hbdShiftFpr = hbdPushFpr

    hbdPushPr :: PrInfo -> Bool
    hbdPushPr info =
      let pPend = pending (prState info) -- current pending formulas
          pPendHbdfs = D.intersect pPend maskHbd -- current pending HBack Down formulas
      in D.null pPendHbdfs

    hbdShiftPr :: PrInfo -> Bool
    hbdShiftPr = hbdPushPr
    --

    -- Alw: Always g --
    maskAlw = D.suchThat bitenc checkAlw
    checkAlw (Always _) = True
    checkAlw _ = False
    alwClos = S.filter checkAlw cl -- all Always g formulas in the closure

    alwCond :: FormulaSet -> Bool
    alwCond clos = not (null [f | f@(Always _) <- S.toList clos])

    alwPushPr :: PrInfo -> Bool
    alwPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pCurrAlwHoldingfs =  S.filter (\g -> D.member bitenc g pCurr) alwClos
          alwArgfs = D.encode bitenc $
                     S.map (\(Always g) -> g)  pCurrAlwHoldingfs

          checkSet = D.intersect  pCurr alwArgfs
      in alwArgfs == checkSet

    alwShiftPr :: PrInfo -> Bool
    alwShiftPr = alwPushPr

    alwPushFcr :: FcrInfo -> Bool
    alwPushFcr info =
      let pCurr = current $ fcrState info
          fCurr = fcrFutureCurr info
          pCurrAlwfs = D.intersect pCurr maskAlw
          fCurrAlwfs = D.intersect fCurr maskAlw
      in pCurrAlwfs == fCurrAlwfs
    alwShiftFcr = alwPushFcr
    alwPopFcr = alwPushFcr

---------------------------------------------------------------------------------
-- present
data PrInfo = PrInfo
  { prState     :: State -- current state
  , prProps     :: Maybe (Input) -- Input is a BitVector-encoded set of AP (note that L(OPA) is in PowerSet(AP))
  , prPopped    :: Maybe (State) -- state to pop
  , prNextProps :: Maybe (Input) -- next input
  }
-- future current
data FcrInfo = FcrInfo
  { fcrState      :: State -- current state
  , fcrProps      :: Maybe (Input) -- input
  , fcrPopped     :: Maybe (State) -- state to pop
  , fcrFutureCurr :: Atom -- future current holding formulas
  , fcrNextProps  :: Maybe (Input) -- next input
  }
-- future pending
data FprInfo = FprInfo
  { fprState          :: State -- current state
  , fprProps          :: Maybe (Input) -- input
  , fprPopped         :: Maybe (State)  -- state to pop
  , fprFuturePendComb :: (EncodedSet, Bool, Bool, Bool) -- future pending obligations (set of formulas to satisfy, mustPush, mustShift, afterPop)
  , fprNextProps      :: Maybe (Input) -- next input
  }
-- future
data FrInfo = FrInfo
  { frState          :: State -- current state
  , frProps          :: Maybe (Input) -- input
  , frPopped         :: Maybe (State) -- state to pop
  , frFutureCurr     :: Atom -- future current holding formulas
  , frFuturePendComb :: (EncodedSet, Bool, Bool, Bool) -- future pending obligations (set of formulas to satisfy, mustPush, mustShift, afterPop)
  , frNextProps      :: Maybe (Input) -- next input
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


-- delta relation of the OPA
delta :: RuleGroup -- rules (shiftRules if we are building deltaShift, ...)
      -> [Atom] -- BitVectors which represent all consistent subsets of the closure of phi
      -> Set (EncodedSet, Bool, Bool, Bool) -- set of future obligations
      -> State -- current state
      -> Maybe Input -- current input (a set of AP)
      -> Maybe State -- for deltaPop, input state (the state on the stack we are popping)
      -> Maybe Input -- future input
      -> [State]
delta rgroup atoms pcombs state mprops mpopped mnextprops = fstates
  where
    prs  = ruleGroupPrs  rgroup -- present rules
    fcrs = ruleGroupFcrs rgroup -- future current rules
    fprs = ruleGroupFprs rgroup -- future pending rules
    frs  = ruleGroupFrs  rgroup -- future rules

    -- all present rules must be satisfied by the current state
    pvalid = all ($ info) prs
      where info = PrInfo { prState     = state,
                            prProps     = mprops,
                            prPopped    = mpopped,
                            prNextProps = mnextprops
                          }
    -- all future current rules must be satisfied by (candidate) future states
    vas = filter valid nextAtoms
      where makeInfo curr = FcrInfo { fcrState      = state,
                                      fcrProps      = mprops,
                                      fcrPopped     = mpopped,
                                      fcrFutureCurr = curr,
                                      fcrNextProps  = mnextprops
                                    }
            valid atom = let info = makeInfo atom
                         in all ($ info) fcrs
            nextAtoms = if isNothing mpopped
                        then atoms
                        else [current state] -- during pops, the current set cannot change
    -- all future pending rules must be satisfied
    vpcs = S.toList . S.filter valid $ pcombs
      where makeInfo pendComb = FprInfo { fprState          = state,
                                          fprProps          = mprops,
                                          fprPopped         = mpopped,
                                          fprFuturePendComb = pendComb,
                                          fprNextProps      = mnextprops
                                        }
            valid pcomb = let info = makeInfo pcomb
                          in all ($ info) fprs

    fstates = if (pvalid)
              then [State curr pend xl xe xr | curr <- vas
                                             , pc@(pend, xl, xe, xr) <- vpcs
                                             , valid curr pc]
              else []
      -- all future rules must be satisfied
      where makeInfo curr pendComb = FrInfo { frState          = state,
                                              frProps          = mprops,
                                              frPopped         = mpopped,
                                              frFutureCurr     = curr,
                                              frFuturePendComb = pendComb,
                                              frNextProps      = mnextprops
                                            }
            valid curr pcomb = let info = makeInfo curr pcomb
                               in all ($ info) frs

-- given a BitEncoding and a state, determine whether it's final
isFinal :: BitEncoding -> State -> Bool
isFinal bitenc s =
  not (mustPush s) -- xe can be instead accepted, as if # = #
  && (not . D.null $ D.intersect currFset maskEnd)
  && (D.null $ D.intersect currFset maskFuture)
  && currPend == (D.intersect currPend mask)
  where
    maskEnd = D.singleton bitenc (Atomic End)
    maskFuture = D.suchThat bitenc future

    maskXbu = D.suchThat bitenc checkXbu
    checkXbu (XBack Up _) = True
    checkXbu _ = False

    maskAlw = D.suchThat bitenc checkAlw
    checkAlw (Always _) = True
    checkAlw _ = False

    currFset = current s
    currPend = pending s
    mask = D.union maskXbu maskAlw
    -- only XBack Up and Always formulas are allowed


---------------------------------------------------------------------------------
check :: Formula APType
      -> [StructPrecRel APType]
      -> [PropSet]
      -> Bool
check phi sprs ts =
  run
    prec
    is
    (isFinal bitenc)
    (deltaShift as pcs shiftRules)
    (deltaPush  as pcs pushRules)
    (deltaPop   as pcs popRules)
    encTs
  where nphi = normalize phi
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



fastcheck :: Formula APType -- the input formula phi
          -> [StructPrecRel APType] -- OPM
          -> [PropSet] -- input tokens
          -> Bool
fastcheck phi sprs ts =
  augRun
    prec
    is
    (isFinal bitenc)
    (augDeltaShift as pcs shiftRules)
    (augDeltaPush  as pcs pushRules)
    (augDeltaPop   as pcs popRules)
    encTs
  where nphi = normalize phi

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

        laProps lookahead = case lookahead of
                              Just npset -> npset
                              Nothing    -> D.encodeInput bitenc $ S.singleton End

        augDeltaShift atoms pcombs rgroup lookahead state props = fstates
          where fstates = delta rgroup atoms pcombs state
                          (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPush atoms pcombs rgroup lookahead state props = fstates
          where fstates = delta rgroup atoms pcombs state
                          (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPop atoms pcombs rgroup lookahead state popped = fstates
          where fstates = delta rgroup atoms pcombs state
                          Nothing (Just popped) (Just . laProps $ lookahead)

fastcheckGen :: ( Ord a, Show a)
             => Formula a -- the input formula phi
             -> [StructPrecRel a] -- OPM
             -> [Set (Prop a)] -- input tokens
             -> Bool
fastcheckGen phi precr ts =
  let (tphi, tprecr, tts) = convPropTokens phi precr ts
  in fastcheck tphi tprecr tts


---------------------------------------------------------------------------------
--- generate an OPA corresponding to a POTL formula
makeOpa ::  Formula APType -- the input formula
        -> ([Prop APType], [Prop APType]) -- AP (structural labels, all other propositions in phi)
        -> [StructPrecRel APType]  -- OPM
        -> (BitEncoding -- data for encoding and decoding between bitsets and formulas and props
           , EncPrecFunc -- OPM on bitsets
           , [State] -- initial states
           , State -> Bool -- isFinal
           , State -> Maybe Input -> [State] -- deltaPush
           , State -> Maybe Input -> [State] -- deltaShift
           , State -> State -> [State] -- deltaPop
           )
makeOpa phi (sls, als) sprs = (bitenc
                              , prec
                              , is
                              , isFinal bitenc
                              , deltaPush  as pcs pushRules      -- apply PushRules
                              , deltaShift as pcs shiftRules     -- apply ShiftRules
                              , deltaPop   as pcs popRules       -- apply PopRules
                              )
  where
        -- remove double negations
        nphi = normalize phi
        -- all the atomic propositions (AP) which make up the language (L is in powerset(AP))
        -- it contains duplicates
        tsprops = sls ++ als
        -- generate the powerset of AP, ech time taking a prop from the structural list
        inputSet = S.fromList [S.fromList (sl:alt) | sl <- sls, alt <- filterM (const [True, False]) als]
        -- generate the closure of the normalized input formulas
        cl = closure nphi tsprops
        -- generate a BitEncoding from the closure
        bitenc = makeBitEncoding cl
        -- generate an EncPrecFunc from a StructPrecRel
        (prec, _) = fromStructEnc bitenc sprs
        --- generate all consistent subsets of cl
        as = genAtoms bitenc cl inputSet
        -- generate all possible pending sets
        pcs = pendCombs bitenc cl
        -- generate initial states
        is = initials nphi cl (as, bitenc)
        -- generate all delta rules of the OPA
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec
        -- generate the deltaPush function (state and props are its parameters)
        deltaPush atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                props Nothing Nothing
        -- generate the deltaShift function (state and props are its parameters)
        deltaShift atoms pcombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs state
                                props Nothing Nothing
        -- generate the deltaPop function (state and popped are its parameters)
        deltaPop atoms pcombs rgroup state popped = fstates
          where fstates = delta rgroup atoms pcombs state
                                Nothing (Just popped) Nothing
