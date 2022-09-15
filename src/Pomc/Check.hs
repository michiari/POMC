{- |
   Module      : Pomc.Check
   Copyright   : 2020-2021 Davide Bergamaschi, Michele Chiari and Francesco Pontiggia
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Check ( fastcheck
                  , fastcheckGen
                  , EncPrecFunc
                  , makeOpa
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel, Alphabet)
import Pomc.Opa (parAugRun)
import Pomc.Potl (Formula(..), Dir(..), negative, negation, atomic, normalize, future, getProps)
import Pomc.Util (safeHead, xor, implies, iff)
import Pomc.Encoding (EncodedSet, PropSet, BitEncoding(..))
import qualified Pomc.Encoding as E
import Pomc.PropConv (APType, convPropTokens)
import Pomc.State (State(..), Input, Atom)

import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Vector as V

import Data.List (foldl', sortOn, (\\))
import qualified Data.HashMap.Strict as M
import Control.Monad (guard)

import qualified Data.Sequence as SQ
import Data.Foldable (toList)

-- import qualified Debug.Trace as DBG

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
        maskSL = E.inputSuchThat bitenc (flip S.member sl)
        -- a function which makes a bitwise AND between a parameter Atom and the mask
        -- to get only the structural labels out of the parameter Atom
        structLabel s = s `E.intersect` maskSL
        -- map the relation between props into a relation between EncodedAtoms
        relMap = M.fromList $ map (\(sl1, sl2, pr) ->
                                     ((encodeProp sl1, encodeProp sl2), pr)) sprs
        -- encode a single atomic proposition into an EncodedAtom
        encodeProp = E.encodeInput bitenc . S.singleton

-- given a Bit Encoding, a set of holding formulas and AP,
-- and the input APs, determine whether the input APs are satisfied by the future holding formulas
compProps :: BitEncoding -> EncodedSet -> Input -> Bool
compProps bitenc fset pset = E.extractInput bitenc fset == pset


-- generate a closure (phi = input formula, otherProps = AP set of the language)
closure :: Formula APType -> [Prop APType] -> [Formula APType]
closure phi otherProps = let  propClos = concatMap (closList . Atomic) (End : otherProps)
                              phiClos  = closList phi
                         in S.toAscList . S.fromList $ propClos ++ phiClos
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

    closList f =
      case f of
        T                  -> [f, Not f]
        Atomic _           -> [f, Not f]
        Not g              -> closList g
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
        Eventually g       -> [f, Not f] ++ closList g
        AuxBack _ g        -> [f, Not f] ++ closList g
        Always _           -> error "Always formulas must be transformed to Eventually formulas."


-- given a formula closure, generate a bitEncoding
makeBitEncoding ::  [Formula APType] -> BitEncoding
makeBitEncoding clos =
  let
      -- positive formulas
      pclos = filter (not . negative) clos

      fetchVec vec i = vec V.! i

      -- Mapping between positive formulas and bits
      pFormulaClos = filter (not . atomic) pclos
      pFormulaVec = V.fromList pFormulaClos
      pFormulaMap = M.fromList (zip pFormulaClos [0..])

      -- Mapping between positive atoms and bits
      pAtomicClos = filter atomic pclos
      pAtomicSorted = sortOn unwrapProp pAtomicClos
      pAtomicVec = V.fromList pAtomicSorted
      pAtomicMap = M.fromList (zip pAtomicSorted [0..])

      unwrapProp :: Formula APType -> Int
      unwrapProp (Atomic End) = 0
      unwrapProp (Atomic (Prop n)) = fromIntegral n
      unwrapProp _ = error "Not a Prop!"

      -- Mapping between positive closure and bits
      pClosVec = pAtomicVec V.++ pFormulaVec
      -- index function of BitEncoding
      pClosLookup phi = fromJust $ M.lookup phi pClosMap
        where pClosMap = pAtomicMap `M.union` M.map (V.length pAtomicVec +) pFormulaMap

  in E.newBitEncoding (fetchVec pClosVec) pClosLookup (V.length pClosVec) (V.length pAtomicVec)

-- generate encoded atoms from a the closure of phi and all possible inputs
genAtoms :: BitEncoding -> [Formula APType] -> [Input] -> [Atom]
genAtoms bitenc clos inputs =
  let -- Consistency checks
      -- each check is partially applied: it still needs an encoded atom to run the check on
      checks =
        [ onlyif (T `elem` clos) (trueCons bitenc)
        , onlyif (not . null $ [f | f@(And _ _)          <- clos]) (andCons bitenc clos)
        , onlyif (not . null $ [f | f@(Or _ _)           <- clos]) (orCons bitenc clos)
        , onlyif (not . null $ [f | f@(Xor _ _)          <- clos]) (xorCons bitenc clos)
        , onlyif (not . null $ [f | f@(Implies _ _)      <- clos]) (impliesCons bitenc clos)
        , onlyif (not . null $ [f | f@(Iff _ _)          <- clos]) (iffCons bitenc clos)
        , onlyif (not . null $ [f | f@(Until _ _ _)      <- clos]) (untilCons bitenc clos)
        , onlyif (not . null $ [f | f@(Since _ _ _)      <- clos]) (sinceCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Down _ _)  <- clos]) (hierUntilDownCons bitenc clos)
        , onlyif (not . null $ [f | f@(HUntil Up _ _)    <- clos]) (hierUntilUpCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Down  _ _) <- clos]) (hierSinceDownCons bitenc clos)
        , onlyif (not . null $ [f | f@(HSince Up _ _)    <- clos]) (hierSinceUpCons bitenc clos)
        ]
        where onlyif cond f = if cond then f else const True
      -- we apply each check to the EncodedAtom eset
      -- all returns True if all the checks return True
      consistent eset = all (\c -> c eset) checks

      -- Make all consistent atoms
      -- given a starting empty sequence and a BitVector representing a set of formulas,
      -- join it with all the atoms in inputs and check consistency
      prependCons as eset =
        let combs = do easet <- inputs
                       let eset' = E.joinInputFormulas easet eset
                       guard (consistent eset')
                       return eset'
        in as SQ.>< (SQ.fromList combs)

  in toList $ if width bitenc - propBits bitenc == 0
              then SQ.fromList inputs
              else foldl' prependCons SQ.empty (E.generateFormulas bitenc)

-- Consistency check functions

-- consistency check for T
trueCons :: BitEncoding -> EncodedSet -> Bool
trueCons bitenc set = not $ E.member bitenc (Not T) set

-- consistency check for (And g h)
andCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
andCons bitenc clos set = not (E.any bitenc consSet set)
                          &&
                          -- if both g and h hold in current atom, then (And g h) must hold as well
                          null [f | f@(And g h) <- clos,
                                 (E.member bitenc g set) &&
                                 (E.member bitenc h set) &&
                                 not (E.member bitenc f set)]

  where -- if (And g h) holds in current atom, then g and h must both hold as well
        consSet (And g h) = not $ E.member bitenc g set && E.member bitenc h set
        consSet _ = False

-- consistency check for (Or g h)
orCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
orCons bitenc clos set = not (E.any bitenc consSet set)
                         &&
                         -- if g or h holds in current atom, then (Or g h) must hold as well
                         null [f | f@(Or g h) <- clos,
                                ((E.member bitenc g set) ||
                                 (E.member bitenc h set)
                                ) && not (E.member bitenc f set)]

  where -- if (Or g h) holds in current atom, then g or h must hold as well
        consSet (Or g h) = not $ E.member bitenc g set || E.member bitenc h set
        consSet _ = False

-- consistency check for (Xor g h)
xorCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
xorCons bitenc clos set = not (E.any bitenc consSet set)
                         &&
                         -- if g xor h holds in current atom, then (Xor g h) must hold as well
                         null [f | f@(Xor g h) <- clos,
                                (xor (E.member bitenc g set)
                                 (E.member bitenc h set))
                                && not (E.member bitenc f set)]
  where -- if (Xor g h) holds in current atom, then g xor h must hold as well
        consSet (Xor g h) = not $ xor (E.member bitenc g set)  (E.member bitenc h set)
        consSet _ = False

-- consistency check for (Implies g h)
impliesCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
impliesCons bitenc clos set = not (E.any bitenc consSet set)
                         &&
                         -- if g implies h holds in current atom, then (Implies g h) must hold as well
                         null [f | f@(Implies g h) <- clos,
                                (implies (E.member bitenc g set)
                                 (E.member bitenc h set))
                                && not (E.member bitenc f set)]
  where -- if (Implies g h) holds in current atom, then g implies h must hold as well
        consSet (Implies g h) = not $ implies (E.member bitenc g set)  (E.member bitenc h set)
        consSet _ = False

-- consistency check for (Iff g h)
iffCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
iffCons bitenc clos set = not (E.any bitenc consSet set)
                         &&
                         -- if g iff h holds in current atom, then (Iff g h) must hold as well
                         null [f | f@(Iff g h) <- clos,
                                (iff (E.member bitenc g set)
                                 (E.member bitenc h set))
                                && not (E.member bitenc f set)]
  where -- if (Iff g h) holds in current atom, then g iff h must hold as well
        consSet (Iff g h) = not $ iff (E.member bitenc g set) ( E.member bitenc h set)
        consSet _ = False

-- consistency check for (Until dir g h)
untilCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
untilCons bitenc clos set = not (E.any bitenc consSet set)
                            &&
                            -- if h holds or (Until dir g h) still holds in the next (chain) position, then (Until dir g h) must hold in the current atom
                            null [f | f@(Until pset g h) <- clos,
                                                            present f pset g h &&
                                                            not (E.member bitenc f set)]
  where  -- if (Until dir g h) holds, then it must be that h holds or (Until dir g h) still holds in the next (chain) position
        present u dir g h = E.member bitenc h set
                             || (E.member bitenc g set
                                 && (E.member bitenc (PNext  dir u) set
                                     || E.member bitenc (XNext dir u) set))
        consSet f@(Until dir g h) = not $ present f dir g h
        consSet _ = False

-- consistency check for (Since dir g h)
sinceCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
sinceCons bitenc clos set = not (E.any bitenc consSet set)
                            &&
                            -- if h holds or (Since dir g h) still holds in the previous (chain) position,
                            -- then (Since dir g h) must hold in the current atom
                            null [f | f@(Since pset g h) <- clos,
                                   present f pset g h &&
                                   not (E.member bitenc f set)]
  where -- if (Since dir g h) holds, then h holds or (Since dir g h)
        -- holds in the previous (chain) position
        present s dir g h = E.member bitenc h set
                             || (E.member bitenc g set
                                 && (E.member bitenc (PBack dir s) set
                                     || E.member bitenc (XBack dir s) set))
        consSet f@(Since dir g h) = not $ present f dir g h
        consSet _ = False

-- consistency check for (HUntil Down g h)
hierUntilDownCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
hierUntilDownCons bitenc clos set = not (E.any bitenc consSet set)
                                     &&
                                     null [f | f@(HUntil Down g h) <- clos,
                                            present f g h &&
                                            not (E.member bitenc f set)]
  where -- if (HUntil Down g h) holds, then or (...) (...) holds
        present hud g h =
          (E.member bitenc h set && E.member bitenc (XNext Up T) set)
          ||
          (E.member bitenc g set && E.member bitenc (HNext Down hud) set)
        consSet f@(HUntil Down g h) = not $ present f g h
        consSet _ = False


-- consistency check for (HUntil Up g h)
hierUntilUpCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
hierUntilUpCons bitenc clos set = not (E.any bitenc consSet set)
                                     &&
                                     null [f | f@(HUntil Up g h) <- clos,
                                            present f g h &&
                                            not (E.member bitenc f set)]
  where -- if (HUntil Up g h) holds, then or (...) (...) holds
        present huu g h =
          (E.member bitenc h set && E.member bitenc (XBack Down T) set)
          ||
          (E.member bitenc g set && E.member bitenc (HNext Up huu) set)
        consSet f@(HUntil Up g h) = not $ present f g h
        consSet _ = False

-- consistency check for (HSince Down g h)
hierSinceDownCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
hierSinceDownCons bitenc clos set = not (E.any bitenc consSet set)
                                    &&
                                    null [f | f@(HSince Down g h) <- clos,
                                           present f g h &&
                                           not (E.member bitenc f set)]
  where present hsd g h =
          (E.member bitenc h set && E.member bitenc (XNext Up T) set)
          ||
          (E.member bitenc g set && E.member bitenc (HBack Down hsd) set)
        consSet f@(HSince Down g h) = not $ present f g h
        consSet _ = False


-- consistency check for (HSince Up g h)
hierSinceUpCons :: BitEncoding -> [Formula APType] -> EncodedSet -> Bool
hierSinceUpCons bitenc clos set = not (E.any bitenc consSet set)
                                     &&
                                     null [f | f@(HSince Up g h) <- clos,
                                            present f g h &&
                                            not (E.member bitenc f set)]
  where present hsu g h =
          (E.member bitenc h set && E.member bitenc (XBack Down T) set)
          ||
          (E.member bitenc g set && E.member bitenc (HBack Up hsu) set)
        consSet f@(HSince Up g h) = not $ present f g h
        consSet _ = False

-- given the BitEncoding and the closure of phi,
-- generate all possible combinations of pending obligations + (mustPush, mustShift, afterPop)
pendCombs :: BitEncoding -> [Formula APType] -> [(EncodedSet, Bool, Bool, Bool)]
pendCombs bitenc clos =
  let checkPend (XNext _ _) = True
      checkPend (XBack _ _) = True
      checkPend (HNext _ _) = True
      checkPend (HBack _ _) = True
      checkPend (AuxBack _ _) = True
      checkPend _ = False

      pendSets = E.powerSet bitenc $ filter checkPend clos
      combs pset = [(pset, xl, xe, xr) | xl <- [False, True]
                                       , xe <- [False, True]
                                       , xr <- [False, True]
                                       , not (xl && xe)]
  in concatMap combs pendSets

-- given the BitEncoding and the closure of phi,
-- generate all possible combinations of instack obligations for the Omega case
stackCombs :: BitEncoding -> [Formula APType] -> [(EncodedSet)]
stackCombs bitenc clos =
  let xns = [f | f@(XNext _ _) <- clos]
  in E.powerSet bitenc xns

-- given phi, its closure, and the set of all consistent atoms, generate all initial states
initials :: Bool -> BitEncoding -> Formula APType -> [Formula APType] -> [Atom] -> [State]
initials isOmega bitenc phi clos atoms =
  let compatible atom =
        let checkNotComp (PBack _ _) = True
            checkNotComp (AuxBack Down _) = True
            checkNotComp (XBack _ _) = True
            checkNotComp _ = False
            maskNotComp = E.suchThat bitenc checkNotComp
        in E.member bitenc phi atom && E.null (E.intersect atom maskNotComp)
           -- phi must be satisfied in the initial state and it must contain no incompatible formulas
      compAtoms = filter compatible atoms
      xndfSets = E.powerSet bitenc [f | f@(XNext Down _) <- clos]
  -- list of all compatible states and the powerset of all possible future obligations
  -- for the Omega case, there are no stack obligations in the initial states
  in if (isOmega)
     then [WState phia phip (E.empty bitenc) True False False
          | phia <- compAtoms, phip <- xndfSets]
     else [FState phia phip True False False
          | phia <- compAtoms, phip <- xndfSets]

-- return all deltaRules b satisfying condition (i -> Bool) on i (a closure)
resolve :: i -> [(i -> Bool, b)] -> [b]
resolve info conditionals = snd . unzip $ filter (\(cond, _) -> cond info) conditionals

-- given a BitEncoding, the closure of phi, and the precedence function, generate all Rule groups: (shift rules, push rules, pop rules)
deltaRules :: BitEncoding -> [Formula APType] -> EncPrecFunc -> (RuleGroup, RuleGroup, RuleGroup)
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
                                     ]
        , ruleGroupFcrs = resolve cl [ (evCond,   evShiftFcr)
                                     ]
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
        , ruleGroupFsrs = resolve cl [(xnCond,   xnShiftFsr)]
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
                                     ]
        , ruleGroupFcrs = resolve cl [ (evCond,   evPushFcr)
                                     ]
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
        , ruleGroupFsrs = resolve cl [(xnCond, xnPushFsr1)
                                     ,(xnCond, xnPushFsr2)]
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
        , ruleGroupFcrs = resolve cl [ (evCond,   evPopFcr)
                                     ]
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
        , ruleGroupFrs  = resolve cl [(hbuCond, hbuPopFr)]
        , ruleGroupFsrs = resolve cl [(xnCond,  xnPopFsr)]
        }
  in (shiftGroup, pushGroup, popGroup)
  where
    -- Auxiliary functions for when we want to check for an operator
    -- depending on another one
    makeOp2OpMap :: (Formula APType -> Formula APType)
                 -> (Formula APType -> Bool)
                 -> [(EncodedSet, EncodedSet, EncodedSet)]
    makeOp2OpMap getAssoc checkOp =
      map makeMasks $ filter checkOp cl
      where makeMasks f =
              let g = getAssoc f
                  gMask = E.singleton bitenc
                          $ if negative g then negation g else g
              in ( E.singleton bitenc f -- mask for f
                 , gMask -- mask for g
                 , if negative g then E.empty bitenc else gMask -- how g should be
                 )
    makeOpCheckSet :: [(EncodedSet, EncodedSet, EncodedSet)]
                   -> EncodedSet
                   -> EncodedSet
    makeOpCheckSet op2OpMap baseSet = foldl'
      (\cset (fMask, gMask, g) -> if E.intersect gMask baseSet == g then E.union cset fMask else cset)
      (E.empty bitenc)
      op2OpMap

    -- XL rules :: PrInfo -> Bool
    xlShiftPr info = not $ mustPush (prState info)
    xlPushPr  info = mustPush (prState info)
    xlPopPr   info = not $ mustPush (prState info)
    --

    -- XE rules :: PrInfo -> Bool
    xeShiftPr info = mustShift (prState info)
    xePushPr  info = not $ mustShift (prState info)
    xePopPr   info = not $ mustShift (prState info)
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

    -- XR rules :: FprInfo -> Bool
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
    pnCond :: [Formula APType] -> Bool
    pnCond clos = not (null [f | f@(PNext _ _) <- clos])

    pnPushFr :: FrInfo -> Bool
    pnPushFr info =
      let pCurr = current $ frState info -- set of formulas that hold in current position
          fCurr = frFutureCurr info -- future current holding formulas
          (_, fXl, fXe, _) = frFuturePendComb info

          -- BitVector where all ones correspond to PNext operators
          maskPn = E.suchThat bitenc checkPn
          checkPn (PNext _ _) = True
          checkPn _ = False

          -- a tuple made of all arguments of PNext formulas in the closure
          pndArgs = V.fromList $ foldl' (getPnDirArg Down) [] cl -- get all the arguments of PNext Down operators
          pnuArgs = V.fromList $ foldl' (getPnDirArg Up) [] cl -- get all the arguments of PNext Up operators
          pnArgs = pndArgs V.++ pnuArgs -- get all the arguments of PNext operators

          getPnDirArg dir rest f@(PNext thisDir g)
            | dir /= thisDir = rest
            | negative g = (True, E.singleton bitenc f, E.singleton bitenc (negation g)) : rest -- negative arguments are put in positive form
            | otherwise  = (False, E.singleton bitenc f, E.singleton bitenc g) : rest
          getPnDirArg _ rest _ = rest

          -- choosePnArgs fXl fXe
          choosePnArgs _ True = pnArgs -- if next move is a shift, any PNext can hold
          choosePnArgs True _ = pndArgs -- if next move is a push, only PNext Down can hold
          choosePnArgs _ _ = pnuArgs -- if next move is a pop, only PNext Up can hold

          pCurrPnfs = E.intersect pCurr maskPn -- current holding PNext formulas
          checkSet = V.foldl' checkSetFold (E.empty bitenc) (choosePnArgs fXl fXe) -- PNext formulas that should currently hold according to future formulas
          checkSetFold acc (negf, fMask, gMask)
            | ((not negf && (not . E.null $ E.intersect gMask fCurr)) -- a positive PNext and the formula g holds in the next state
                || (negf && (E.null $ E.intersect gMask fCurr))) -- or a negative PNext and the formula g does not hold in the next state
            = E.union acc fMask
            | otherwise = acc

      in pCurrPnfs == checkSet -- if PNext g holds in the current state, then g must hold in the next state, and viceversa

    pnShiftFr :: FrInfo -> Bool
    pnShiftFr = pnPushFr
    --

    -- PB rules --
    pbCond :: [Formula APType] -> Bool
    pbCond clos = not (null [f | f@(PBack _ _) <- clos])

    pbPushFr :: FrInfo -> Bool
    pbPushFr info =
      let pCurr = current $ frState info -- BitVector of formulas holding in current position
          fCurr = frFutureCurr info -- future current holding formulas
          (_, fXl, fXe, _) = frFuturePendComb info

          -- a BitVector where all ones correspond to PBack operators
          maskPb = E.suchThat bitenc checkPb
          checkPb (PBack _ _) = True
          checkPb _ = False

          -- a tuple made of all arguments of PBack formulas in the closure
          pbdArgs = V.fromList $ foldl' (getPbDirArg Down) [] cl -- get all the arguments of PBack Down operators
          pbuArgs = V.fromList $ foldl' (getPbDirArg Up) [] cl -- get all the arguments of PBack Up operators
          pbArgs = pbdArgs V.++ pbuArgs -- get all the arguments of PBack operators

          getPbDirArg dir rest f@(PBack thisDir g)
            | dir /= thisDir = rest
            | negative g = (True, E.singleton bitenc f, E.singleton bitenc (negation g)) : rest -- negative arguments are put in positive form
            | otherwise  = (False, E.singleton bitenc f, E.singleton bitenc g) : rest
          getPbDirArg _ rest _ = rest

          -- choosePbArgs fXl fXe
          choosePbArgs _ True = pbArgs -- if next move is a shift, any PBack can hold
          choosePbArgs True _ = pbdArgs -- if next move is a push, only PBack Down can hold
          choosePbArgs _ _ = pbuArgs -- if next move is a pop, only PBack Up can hold

          fCurrPbfs = E.intersect fCurr maskPb -- PBack formulas holding in the next state
          checkSet = V.foldl' checkSetFold (E.empty bitenc) (choosePbArgs fXl fXe) -- future PBack formulas according to present formulas
          checkSetFold acc (negf, fMask, gMask)
            | ((not negf && (not . E.null $ E.intersect gMask pCurr)) -- a positive PBack and the formula g holds in the next state
                || (negf && (E.null $ E.intersect gMask pCurr))) -- or a negative PBack and the formula g does not hold in the next state
            = E.union acc fMask
            | otherwise = acc

      in fCurrPbfs == checkSet -- if PBack g holds in the current state, then g must hold in the next state, and viceversa

    pbShiftFr = pbPushFr

    --rules for the omega case
    --XN: XNext _
    --get a mask with all XNext _ formulas set to one
    maskXn = E.suchThat bitenc checkXn
    checkXn (XNext _ _) = True
    checkXn _ = False

    xnCond clos = not (null [f | f@(XNext _ _) <- clos])

    -- rules only for the omega case
    -- stack sets can contain only XNext _ _ formulas,
    -- so there is no need to intersect pPend with maskxn
    -- xnPush1 :: FsrInfo -> Bool
    xnPushFsr1 info =
      let pPend = pending $ fsrState info
          pPendXnfs = E.intersect pPend maskXn
          fStack = fsrFutureStack info
      in E.intersect pPendXnfs fStack == pPendXnfs

    -- xnPush2 :: FsrInfo -> Bool
    xnPushFsr2 info =
      let pStack = stack $ fsrState info
          fStack = fsrFutureStack info
      in E.intersect pStack fStack == pStack

    -- xnShiftFsr :: FsrInfo -> Bool
    xnShiftFsr = xnPushFsr2

    -- xnPopFsr :: FsrInfo -> Bool
    xnPopFsr info =
      let pStack = stack $ fsrState info
          ppStack = stack $ fromJust (fsrPopped info)
          fStack = fsrFutureStack info
          checkSet = E.intersect pStack ppStack
      in  E.intersect checkSet fStack == checkSet
    -- end of rules for the omega case

    -- XND: XNext Down --
    -- get a mask with all XNext Down formulas set to one
    maskXnd = E.suchThat bitenc checkXnd
    g2xndg = makeOp2OpMap (\(XNext _ g) -> g) checkXnd
    checkXnd (XNext Down _) = True
    checkXnd _ = False

    -- check whether we have some XNext Down in the closure
    xndCond :: [Formula APType] -> Bool
    xndCond clos = not (null [f | f@(XNext Down _) <- clos])

    xndPushFpr :: FprInfo -> Bool
    xndPushFpr info =
      let pCurr = current $ fprState info -- current holding propositions
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          pCurrXndfs = E.intersect pCurr maskXnd -- current holding XNext Down formulas
          fPendXndfs = E.intersect fPend maskXnd -- future pending XNext Down obligations

      in if fXl -- if nextState mustPush
           then pCurrXndfs == fPendXndfs
           else E.null pCurrXndfs -- if not mustPush, then here mustn't be XNext Down formulas

    xndShiftFpr = xndPushFpr

    xndPopFpr :: FprInfo -> Bool
    xndPopFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          ppPendXndfs = E.intersect maskXnd ppPend -- all XNext Down pending obligations of state to pop

          pCheckSet = makeOpCheckSet g2xndg pCurr -- get all (XNext Down g) formulas of the closure such that g currently holds
          fCheckSet = E.intersect fPend maskXnd -- future XNext Down pending obligations
          checkSet = E.union pCheckSet fCheckSet -- or (future XNext Down pending obligation) (XNext Down g such that g currently hold)

      in if fXl -- if next state mustPush
         then ppPendXndfs == checkSet -- all XNext Down pending obligations of state to pop are valid if or ...
         else ppPendXndfs == fCheckSet -- all XNext Down pending obligations of state to pop are valid if they hold as pending obligations in the next state

    xndPopPr :: PrInfo -> Bool
    xndPopPr info =
      let pPend = pending $ prState info -- current pending obligations
          pPendXndfs = E.intersect pPend maskXnd --current pending XNext Down obligations
      in  E.null pPendXndfs -- no pending XNext Down is allowed in current state when popping

    xndShiftPr :: PrInfo -> Bool
    xndShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending obligations
          pPendXndfs = E.intersect pPend maskXnd -- current pending XNext Down obligations
          pCheckSet = makeOpCheckSet g2xndg pCurr -- get all (XNext Down g) formulas of the closure such that g currently holds
      in pCheckSet == pPendXndfs -- XNext Down g is a current pending obligation iff g holds in the current state

    --
    -- XNU: XNext Up
    -- get a mask with all XNext Up formulas set to one
    maskXnu = E.suchThat bitenc checkXnu
    checkXnu (XNext Up _) = True
    checkXnu _ = False

    -- check whether we have some XNext Up in the closure
    xnuCond :: [Formula APType] -> Bool
    xnuCond clos = not (null [f | f@(XNext Up _) <- clos])

    xnuPushFpr :: FprInfo -> Bool
    xnuPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXnufs = E.intersect fPend maskXnu -- future pending XNext Up obligations
          pCurrXnufs = E.intersect pCurr maskXnu -- current holding XNext Up formulas
      in if fXl -- if next state must push
           then pCurrXnufs == fPendXnufs
           else E.null pCurrXnufs -- if not mustPush, then here mustn't be XNext Down formulas

    xnuShiftFpr :: FprInfo -> Bool
    xnuShiftFpr = xnuPushFpr

    xnuPopPr :: PrInfo -> Bool
    xnuPopPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending (prState info) --current pending obligations
          pPendXnufs = E.intersect pPend maskXnu -- current pending XNext Up obligations

          g2xnug = makeOp2OpMap (\(XNext _ g) -> g) checkXnu
          pCheckSet = makeOpCheckSet g2xnug pCurr -- all (XNext Up g) such that g currently holds
      in pCheckSet == pPendXnufs

    xnuPopFpr :: FprInfo -> Bool
    xnuPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendXnufs = E.intersect ppPend maskXnu -- XNext Up pending obligations of state to pop
          fPendXnufs = E.intersect fPend maskXnu -- XNext Up future pending obligations
      in ppPendXnufs == fPendXnufs

    xnuShiftPr :: PrInfo -> Bool
    xnuShiftPr = xnuPopPr

    --
    -- XBD: XBack Down
    -- get a mask with all XBack Down set to one
    maskXbd = E.suchThat bitenc checkXbd
    checkXbd (XBack Down _) = True
    checkXbd _ = False

    xbdCond :: [Formula APType] -> Bool
    xbdCond clos = not (null [f | f@(XBack Down _) <- clos])

    xbdPushPr :: PrInfo -> Bool
    xbdPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending obligations
          pXr = afterPop (prState info) -- was the previous transition a pop?
          pCurrXbdfs = E.intersect pCurr maskXbd -- current holding XBack Down formulas
          pPendXbdfs = E.intersect pPend maskXbd -- current pending XBack Down formulas
      in if pXr
         then pCurrXbdfs == pPendXbdfs
         else E.null pCurrXbdfs

    xbdShiftPr :: PrInfo -> Bool
    xbdShiftPr = xbdPushPr

    xbdPopFpr :: FprInfo -> Bool
    xbdPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending obligations of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendXbdfs = E.intersect ppPend maskXbd -- XBack Down pending obligations of state to pop
          fPendXbdfs = E.intersect fPend maskXbd -- XBack Down future pending obligations
      in ppPendXbdfs == fPendXbdfs

    xbdPushFpr :: FprInfo -> Bool
    xbdPushFpr info =
      let pCurr = current $ fprState info --current holding formulas
          (fPend, _, _, _) = fprFuturePendComb info -- future pending formulas
          fPendXbdfs = E.intersect fPend maskXbd -- future pending XBack Down formulas
          g2xbdg = makeOp2OpMap (\(XBack _ g) -> g) checkXbd
          pCheckSet = makeOpCheckSet g2xbdg pCurr -- all (XBack Down g) such that g currently holds
      in fPendXbdfs == pCheckSet

    xbdShiftFpr :: FprInfo -> Bool
    xbdShiftFpr = xbdPushFpr

    --
    -- XBU: XBack Up
    -- a mask with all XBack Up formulas set to True
    maskXbu = E.suchThat bitenc checkXbu
    checkXbu (XBack Up _) = True
    checkXbu _ = False

    -- checking whether there are XBack Up formulas in the closure
    xbuCond :: [Formula APType] -> Bool
    xbuCond clos = not (null [f | f@(XBack Up _) <- clos])

    xbuPushFpr :: FprInfo -> Bool
    xbuPushFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXbufs = E.intersect fPend maskXbu
      in E.null fPendXbufs

    xbuShiftFpr :: FprInfo -> Bool
    xbuShiftFpr = xbuPushFpr

    xbuPushPr :: PrInfo -> Bool
    xbuPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pXr = afterPop $ prState info  -- was the previous transition a pop?
          pCurrXbufs = E.intersect pCurr maskXbu -- current holding XBack Up formulas
          pPendXbufs = E.intersect pPend maskXbu -- current pending XBack Up formulas
      in if pXr
           then pCurrXbufs == pPendXbufs
           else E.null pCurrXbufs

    xbuShiftPr :: PrInfo -> Bool
    xbuShiftPr = xbuPushPr

    xbuPopFpr :: FprInfo -> Bool
    xbuPopFpr info =
      let pPend = pending (fprState info) -- current pending obligations
          pPendXbufs = E.intersect pPend maskXbu -- current XBack Up pending obligations
          (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          fPendXbufs = E.intersect fPend maskXbu -- future XBack Up pending obligations

          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in the state to pop
          abd2xbu = makeOp2OpMap (\(XBack Up g) -> AuxBack Down g) checkXbu
          ppCheckSet = makeOpCheckSet abd2xbu ppCurr -- get all (XBack Up g) such that (AuxBack Down g) currently holds in state to pop
          checkSet = E.union ppCheckSet pPendXbufs
      in if fXl
         then pPendXbufs == fPendXbufs
         else fPendXbufs == checkSet

    --
    -- ABD: AuxBack Down
    maskAbd = E.suchThat bitenc checkAbd
    checkAbd (AuxBack Down _) = True
    checkAbd _ = False

    abdCond :: [Formula APType] -> Bool
    abdCond clos = not (null [f | f@(AuxBack Down _) <- clos])

    abdPushPr :: PrInfo -> Bool
    abdPushPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pCurrAbdfs = E.intersect pCurr maskAbd -- currently holding AuxBack Down formulas
          pPendAbdfs = E.intersect pPend maskAbd -- currently pending AuxBack Down formulas
      in
        pCurrAbdfs == pPendAbdfs

    abdShiftPr :: PrInfo -> Bool
    abdShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
      in E.null $ E.intersect pCurr maskAbd -- no AuxBack Down formulas are allowed when shifting

    abdPopFpr :: FprInfo -> Bool
    abdPopFpr info =
      let ppPend = pending $ fromJust (fprPopped info) -- pending formulas of state to pop
          (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppPendAbdfs = E.intersect ppPend maskAbd -- pending AuxBack Down formulas of state to pop
          fPendAbdfs = E.intersect fPend maskAbd -- future pending AuxBack Down formulas
      in ppPendAbdfs == fPendAbdfs

    abdPushFpr :: FprInfo -> Bool
    abdPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (fPend, _, _, _) = fprFuturePendComb info -- future pending formulas
          fPendAbdfs = E.intersect fPend maskAbd -- future pending AuxBack Down formulas

          g2abdg = makeOp2OpMap (\(AuxBack _ g) -> g) checkAbd
          pCheckSet = makeOpCheckSet g2abdg pCurr -- get all (AuxBack Down g) such that g currently holds

      in fPendAbdfs == pCheckSet

    abdShiftFpr :: FprInfo -> Bool
    abdShiftFpr = abdPushFpr

    --
    -- HNU: HNext Up
    -- a mask with all HNext Up formulas set to one
    maskHnu = E.suchThat bitenc checkHnu
    checkHnu (HNext Up _) = True
    checkHnu _ = False

    hnuCond :: [Formula APType] -> Bool
    hnuCond clos = not (null [f | f@(HNext Up _) <- clos])

    hnuPushPr1 :: PrInfo -> Bool
    hnuPushPr1 info =
      let pCurr = current $ prState info -- current holding formulas
          pCurrHnufs = E.intersect pCurr maskHnu -- current holding HNext Up formulas
          pXr = afterPop (prState info) -- was the last transition a pop?
      in if not $ E.null pCurrHnufs
           then pXr
           else True

    hnuPushPr2 :: PrInfo -> Bool
    hnuPushPr2 info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formulas
          pXr = afterPop $ prState info -- was the last transition a pop?
          pPendHnufs = E.intersect pPend maskHnu -- current pending HNext Up formulas

          g2hnug = makeOp2OpMap (\(HNext _ g) -> g) checkHnu
          checkSet = makeOpCheckSet g2hnug pCurr -- all (HNext Up g) such that g currently holds
      in if pXr
           then pPendHnufs == checkSet
           else E.null pPendHnufs

    hnuPopFpr :: FprInfo -> Bool
    hnuPopFpr info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- formulas currently holding in state to pop
          ppXr = afterPop $ fromJust (fprPopped info) -- did the state to pop came from a pop transition?
          fPendHnufs = E.intersect fPend maskHnu -- all future pending HNext Up formulas
          ppCurrHnufs = E.intersect ppCurr maskHnu -- HNext Up formulas holding in state to pop
      in if ppXr
         then ppCurrHnufs == fPendHnufs
        else True

    hnuPopPr :: PrInfo -> Bool
    hnuPopPr info =
      let pPend = pending (prState info) -- current pending obligations
          pPendHnufs = E.intersect pPend maskHnu -- current HNext Up pending obligations
      in E.null pPendHnufs -- no HNext Up obligations are allowed when popping

    hnuShiftPr :: PrInfo -> Bool
    hnuShiftPr info =
      let pCurr = current $ prState info -- current holding formulas
          pPend = pending $ prState info -- current pending formuals
          pCurrHnufs = E.intersect pCurr maskHnu -- current HNext Up holding formulas
          pPendHnufs = E.intersect pPend maskHnu -- current HNext Up pending formuals
      in E.null pCurrHnufs && E.null pPendHnufs -- no pending or holding HNext Up formulas are allowed when shifting

    --
    -- HBU: HBack Up
    -- a mask with all XBack Up formulas set to one
    maskHbu = E.suchThat bitenc checkHbu
    checkHbu (HBack Up _) = True
    checkHbu _ = False

    hbuCond :: [Formula APType] -> Bool
    hbuCond clos = not (null [f | f@(HBack Up _) <- clos])

    hbuPushPr :: PrInfo -> Bool
    hbuPushPr info =
      let pCurr = current $ prState info --current holding formulas
          pXl = mustPush $ prState info -- mustPush?
          pXr = afterPop $ prState info -- was the last transition a pop?
          pCurrHbufs = E.intersect pCurr maskHbu --currently holding HBack Up formulas

      in if not $ E.null $ pCurrHbufs
         then pXl && pXr
         else True

    hbuPopFr ::  FrInfo -> Bool
    hbuPopFr info =
      let (_, fXl, _, _) = frFuturePendComb info -- future pending obligations
          fCurr = frFutureCurr info -- future current holding formulas
          ppCurr = current $ fromJust (frPopped info) -- holding formulas in state to pop
          ppXr = afterPop $ fromJust (frPopped info) -- did the state to pop come from a pop?
          fCurrHbufs = E.intersect fCurr maskHbu -- future current holding XBack Up formulas

          g2hbug = makeOp2OpMap (\(HBack Up g) -> g) checkHbu
          checkSet = makeOpCheckSet g2hbug ppCurr -- all (HBack Up g) such that g holds in state to pop
      in if fXl
         then (if ppXr
              then fCurrHbufs == checkSet
              else E.null fCurrHbufs)
         else True

    hbuShiftPr :: PrInfo -> Bool
    hbuShiftPr info =
      let pCurr = current $ prState info --current holding states
          pCurrHbufs = E.intersect pCurr maskHbu -- currently holding HBack Up formulas
      in E.null  $ pCurrHbufs -- no holding HBack Up is allowed when shifting

    --
    -- HND: HNext Down
    -- a mask with all HNext Down formulas set to one
    maskHnd = E.suchThat bitenc checkHnd
    checkHnd (HNext Down _) = True
    checkHnd _ = False

    hndCond :: [Formula APType] -> Bool
    hndCond clos = not (null [f | f@(HNext Down _) <- clos])

    hndPopFpr1 :: FprInfo -> Bool
    hndPopFpr1 info =
      let (fPend, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          fPendHndfs = E.intersect fPend maskHnd -- future pending HNext Down obligations

          abdg2hndg = makeOp2OpMap (\(HNext Down g) -> AuxBack Down g) checkHnd
          checkSet = makeOpCheckSet abdg2hndg ppCurr -- all (HNext Down g) formulas such that AuxBack Down g holds in state to pop
      in if not fXl && not fXe
           then fPendHndfs == checkSet
           else True

    hndPopFpr2 :: FprInfo -> Bool
    hndPopFpr2 info =
      let pPend = pending (fprState info) -- current pending obligations
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- current holding formulas in state to pop

          pPendHndfs = E.intersect pPend maskHnd  -- current pending HNext Down formulas

          abdhndg2hndg = makeOp2OpMap (\f -> AuxBack Down f) checkHnd
          checkSet = makeOpCheckSet abdhndg2hndg ppCurr -- all HNext Down g such that AuxBack Down (HNext Down g) holds in state to pop
      in if not fXl && not fXe
         then pPendHndfs == checkSet
         else True

    hndPopFpr3 :: FprInfo -> Bool
    hndPopFpr3 info =
      let (_, _, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- current holding formulas in state to pop
          abdhndg2hndg = makeOp2OpMap (\f -> AuxBack Down f) checkHnd
          checkSet = makeOpCheckSet abdhndg2hndg ppCurr -- all HNext Down g formulas such that AuxBack Down (HNext Down g) holds in state to pop
      in if not (E.null checkSet)
           then not fXe
           else True

    hndPushFpr1 :: FprInfo -> Bool
    hndPushFpr1 info =
      let pCurr = current $ fprState info -- current holding formulas
          (_, fXl, _, _) = fprFuturePendComb info -- future pending obligations
      in if not $ E.null $ E.intersect pCurr maskHnd
         then fXl
         else True

    hndShiftFpr1 :: FprInfo -> Bool
    hndShiftFpr1 = hndPushFpr1

    hndPushFpr2 :: FprInfo -> Bool
    hndPushFpr2 info =
      let (fPend, _, _, _) = fprFuturePendComb info -- future pending obligations
          fPendHndfs = E.intersect fPend maskHnd -- future pending HNext Down obligations
      in E.null fPendHndfs

    hndShiftFpr2 :: FprInfo -> Bool
    hndShiftFpr2 = hndPushFpr2
    --

    -- HBD: HBack Down
    -- a mask with all HBack Down formulas set to one
    maskHbd = E.suchThat bitenc checkHbd
    checkHbd (HBack Down _) = True
    checkHbd _ = False

    hbdCond :: [Formula APType] -> Bool
    hbdCond clos = not (null [f | f@(HBack Down _) <- clos])

    hbdPopFpr1 :: FprInfo -> Bool
    hbdPopFpr1 info =
      let pPend = pending (fprState info) -- current pending formulas
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          pPendHbdfs = E.intersect pPend maskHbd -- current pending HBack Down formulas

          abdg2hbdg = makeOp2OpMap (\(HBack _ g) -> AuxBack Down g) checkHbd
          checkSet = makeOpCheckSet abdg2hbdg ppCurr -- all (HBack Down g) formulas such that (AuxBack Down g) holds in state to pop
      in if not fXl && not fXe
           then pPendHbdfs == checkSet
           else True

    hbdPopFpr2 :: FprInfo -> Bool
    hbdPopFpr2 info =
      let (fPend, fXl, _, _) = fprFuturePendComb info -- future pending obligations
          ppCurr = current $ fromJust (fprPopped info) -- holding formulas in state to pop

          fPendHbdfs = E.intersect fPend maskHbd -- future pending HBack Down formulas

          abdhbdg2hbdg = makeOp2OpMap (\f -> AuxBack Down f) checkHbd
          checkSet = makeOpCheckSet abdhbdg2hbdg ppCurr -- all (HBack Down g) formulas such that (AuxBack Down (HBack Down g)) holds in state to pop
      in if not fXl
           then fPendHbdfs == checkSet
           else True

    hbdPopFpr3 :: FprInfo -> Bool
    hbdPopFpr3 info =
      let pPend = pending (fprState info) -- current pending formulas
          (_, fXl, fXe, _) = fprFuturePendComb info -- future pending obligations
          pPendHbdfs = E.intersect pPend maskHbd -- current pending HBack Down formulas
      in if not (E.null pPendHbdfs)
           then not fXl && not fXe
           else True

    hbdPushFpr :: FprInfo -> Bool
    hbdPushFpr info =
      let pCurr = current $ fprState info -- current holding formulas
          (_, fXl, _, _) = fprFuturePendComb info -- future pending obligations
      in if not $ E.null $ E.intersect pCurr maskHbd
         then fXl
         else True

    hbdShiftFpr :: FprInfo -> Bool
    hbdShiftFpr = hbdPushFpr

    hbdPushPr :: PrInfo -> Bool
    hbdPushPr info =
      let pPend = pending (prState info) -- current pending formulas
          pPendHbdfs = E.intersect pPend maskHbd -- current pending HBack Down formulas
      in E.null pPendHbdfs

    hbdShiftPr :: PrInfo -> Bool
    hbdShiftPr = hbdPushPr
    --

    -- Ev: Eventually g --
    maskEv = E.suchThat bitenc checkEv
    checkEv (Eventually _) = True
    checkEv _ = False

    evCond :: [Formula APType] -> Bool
    evCond clos = not (null [f | f@(Eventually _) <- clos])

    evPushFcr :: FcrInfo -> Bool
    evPushFcr info =
      let pCurr = current $ fcrState info
          fCurr = fcrFutureCurr info
          pCurrEvfs = E.intersect pCurr maskEv
          evg2g = makeOp2OpMap (\(Eventually g) -> g) checkEv
          pCheckSet = makeOpCheckSet evg2g pCurr
          fCheckSet = E.intersect fCurr maskEv
          checkSet = E.union pCheckSet fCheckSet
      in pCurrEvfs ==  checkSet
    evShiftFcr = evPushFcr
    evPopFcr info =
      let pCurr = current $ fcrState info
          fCurr = fcrFutureCurr info
          pCurrEvfs = E.intersect pCurr maskEv
          fCheckSet = E.intersect fCurr maskEv
      in pCurrEvfs ==  fCheckSet
---------------------------------------------------------------------------------
-- present
data PrInfo = PrInfo
  { prState     :: State -- current state
  , prProps     :: Maybe Input -- current input
  }
-- future current
data FcrInfo  = FcrInfo
  { fcrState      :: State-- current state
  , fcrFutureCurr :: Atom -- future current holding formulas
  , fcrNextProps  :: Maybe Input -- next input
  }
-- future pending
data FprInfo  = FprInfo
  { fprState          :: State -- current state
  , fprPopped         :: Maybe State  -- state to pop
  , fprFuturePendComb :: (EncodedSet, Bool, Bool, Bool) -- future pending obligations (set of formulas to satisfy, mustPush, mustShift, afterPop)
  }
-- future
data FrInfo = FrInfo
  { frState          :: State -- current state
  , frProps          :: Maybe Input -- input
  , frPopped         :: Maybe State -- state to pop
  , frFutureCurr     :: Atom -- future current holding formulas
  , frFuturePendComb :: (EncodedSet, Bool, Bool, Bool) -- future pending obligations (set of formulas to satisfy, mustPush, mustShift, afterPop)
  }

-- future stack
data FsrInfo = FsrInfo
  { fsrState          :: State -- current state
  , fsrPopped         :: Maybe State -- state to pop
  , fsrFutureStack    :: EncodedSet -- future stack obligations (set of formulas to satisfy)
  }

type PresentRule       = (PrInfo  -> Bool)
type FutureCurrentRule = (FcrInfo -> Bool)
type FuturePendingRule = (FprInfo -> Bool)
type FutureRule        = (FrInfo  -> Bool)
type FutureStackRule   = (FsrInfo -> Bool)


data RuleGroup = RuleGroup { ruleGroupPrs  :: [PresentRule      ]
                           , ruleGroupFcrs :: [FutureCurrentRule]
                           , ruleGroupFprs :: [FuturePendingRule]
                           , ruleGroupFrs  :: [FutureRule       ]
                           , ruleGroupFsrs :: [FutureStackRule  ]
                           }


augDeltaRules ::  BitEncoding -> [Formula APType] -> EncPrecFunc -> (RuleGroup, RuleGroup, RuleGroup)
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
      -> [Atom] -- BitVectors which represent all consistent subsets of the closure of phi, alis all the states
      -> [(EncodedSet, Bool, Bool, Bool)] -- set of future obligations
      -> [(EncodedSet)] -- set of instack obligations for the omega case
      -> State -- current state
      -> Maybe Input -- current input (a set of AP)
      -> Maybe State -- for deltaPop, input state (the state on the stack we are popping)
      -> Maybe Input -- future input (for fast functions)
      -> [State]
delta rgroup atoms pcombs scombs state mprops mpopped mnextprops
  | (FState {}) <- state = fstates
  | (WState {}) <- state = wfstates
  where
    prs  = ruleGroupPrs  rgroup -- present rules
    fcrs = ruleGroupFcrs rgroup -- future current rules
    fprs = ruleGroupFprs rgroup -- future pending rules
    frs  = ruleGroupFrs  rgroup -- future rules
    fsrs = ruleGroupFsrs rgroup -- future stack rules

    -- all present rules must be satisfied by the current state
    pvalid = all ($ info) prs
      where info = PrInfo { prState = state
                          , prProps = mprops
                          }
    -- all future current rules must be satisfied by (candidate) future states
    vas = filter valid nextAtoms
      where makeInfo curr = FcrInfo { fcrState      = state
                                    , fcrFutureCurr = curr
                                    , fcrNextProps  = mnextprops
                                    }
            valid atom = let info = makeInfo atom
                         in all ($ info) fcrs
            nextAtoms = if isNothing mpopped
                        then atoms
                        else [current state] -- during pops, the current set cannot change
    -- all future pending rules must be satisfied
    vpcs = filter valid pcombs
      where makeFprInfo pendComb = FprInfo { fprState          = state
                                           , fprPopped         = mpopped
                                           , fprFuturePendComb = pendComb
                                           }
            valid pcomb = let info = makeFprInfo pcomb
                          in all ($ info) fprs

    fstates = if (pvalid)
              then [FState curr pend xl xe xr | curr <- vas
                                              , pc@(pend, xl, xe, xr) <- vpcs
                                              , valid curr pc]
              else []
      -- all future rules must be satisfied
      where makeInfo curr pendComb = FrInfo { frState          = state
                                            , frProps          = mprops
                                            , frPopped         = mpopped
                                            , frFutureCurr     = curr
                                            , frFuturePendComb = pendComb
                                            }
            valid curr pcomb = let info = makeInfo curr pcomb
                               in all ($ info) frs
    -- omega case
    -- all future stack rules must be satisfied
    vscs = filter valid scombs
      where makeFsrInfo stackComb = FsrInfo { fsrState       = state
                                            , fsrPopped      = mpopped
                                            , fsrFutureStack = stackComb
                                            }
            valid scomb = let info = makeFsrInfo scomb
                          in all ($ info) fsrs

    wfstates = if (pvalid)
                then [WState curr pend st xl xe xr | curr <- vas,
                                                     pc@(pend, xl, xe, xr) <- vpcs,
                                                     st <- vscs,
                                                     valid curr pc]
                else []
      -- all future rules must be satisfied
      where makeInfo curr pendComb = FrInfo { frState          = state
                                            , frProps          = mprops
                                            , frPopped         = mpopped
                                            , frFutureCurr     = curr
                                            , frFuturePendComb = pendComb
                                            }
            valid curr pcomb = let info = makeInfo curr pcomb
                               in all ($ info) frs

-- given a BitEncoding, a state formula, determine whether the state is final
isFinal :: BitEncoding ->  Formula APType -> State  -> Bool
isFinal bitenc _   s@(FState {}) = isFinalF bitenc s
isFinal bitenc phi s@(WState {}) = isFinalW bitenc phi s

-- determine whether a state is final for a formula, for the omega case
isFinalW :: BitEncoding -> Formula APType -> State  -> Bool
isFinalW bitenc phi@(XNext Down g) s =
  (not $ E.member bitenc phi (stack s))
  && ((not $ E.member bitenc phi (pending s)) || E.member bitenc g (current s))
isFinalW bitenc phi@(XNext Up _) s =
  (not $ E.member bitenc phi (stack s)) && (not $ E.member bitenc phi (pending s))
isFinalW bitenc phi@(Until Down _ h) s =
  isFinalW bitenc (XNext Down phi) s
  && ((not $ E.member bitenc phi (current s)) || E.member bitenc h (current s))
isFinalW bitenc phi@(Until Up _ h) s =
  isFinalW bitenc (XNext Up phi) s
  && ((not $ E.member bitenc phi (current s)) || E.member bitenc h (current s))
isFinalW bitenc phi@(Eventually g) s =
  (E.member bitenc g (current s)) || (not $ E.member bitenc phi (current s))
isFinalW _ _ _ = True

-- given a BitEncoding and a state, determine whether the state is final
isFinalF :: BitEncoding -> State -> Bool
isFinalF bitenc s =
  not (mustPush s) -- xe can be instead accepted, as if # = #
  && (not . E.null $ E.intersect currFset maskEnd)
  && (E.null $ E.intersect currFset maskFuture)
  && currPend == (E.intersect currPend maskXbu)
  where
    maskEnd = E.singleton bitenc (Atomic End)
    maskFuture = E.suchThat bitenc future

    maskXbu = E.suchThat bitenc checkXbu
    checkXbu (XBack Up _) = True
    checkXbu _ = False

    currFset = current s
    currPend = pending s
    -- only XBack Up formulas are allowed in pending part of final states

---------------------------------------------------------------------------------
-- fastCheck performs trace checking using a lookahead to predict future inputs
fastcheck :: Formula APType -- the input formula phi
          -> [StructPrecRel APType] -- OPM
          -> [PropSet] -- input tokens
          -> Bool
fastcheck phi sprs ts =
  parAugRun
    prec
    is
    (isFinalF bitenc)
    (augDeltaShift as pcs scs shiftRules)
    (augDeltaPush  as pcs scs pushRules)
    (augDeltaPop   as pcs scs popRules)
    encTs
  where nphi = normalize phi
        tsprops = S.toList $ foldl' (S.union) S.empty (sl:ts)
        encTs = map (E.encodeInput bitenc) ts
        inputSet = S.toList . S.fromList
          $ (E.singletonInput bitenc End):encTs

        -- generate the closure of the normalized input formula
        cl = closure nphi tsprops
        -- generate a BitEncoding from the closure
        bitenc = makeBitEncoding cl
        -- generate all possible stack obligations for the omega case
        scs = stackCombs bitenc cl
        -- generate an EncPrecFunc from a StructPrecRel
        (prec, sl) = fromStructEnc bitenc sprs
        -- generate all consistent subsets of cl
        as = genAtoms bitenc cl inputSet
        -- generate all possible pending obligations
        pcs = pendCombs bitenc cl
        is = filter compInitial (initials False bitenc nphi cl as)
        (shiftRules, pushRules, popRules) = augDeltaRules bitenc cl prec

        compInitial s = fromMaybe True $
                          (compProps bitenc) <$> (Just . current) s <*> safeHead encTs

        laProps lookahead = case lookahead of
                              Just npset -> npset
                              Nothing    -> E.encodeInput bitenc $ S.singleton End

        augDeltaShift atoms pcombs scombs rgroup lookahead state props = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                          (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPush atoms pcombs scombs rgroup lookahead state props = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                          (Just props) Nothing (Just . laProps $ lookahead)

        augDeltaPop atoms pcombs scombs rgroup lookahead state popped = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                          Nothing (Just popped) (Just . laProps $ lookahead)

-- fastcheckGen is just fastcheck, but parametric in the type of formula
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
makeOpa :: Formula APType -- the input formula
        -> Bool -- is it opba?
        -> Alphabet APType -- OP alphabet
        -> (BitEncoding -> Input -> Bool)
        -> ( BitEncoding -- data for encoding and decoding between bitsets and formulas and props
           , EncPrecFunc -- OPM on bitsets
           , [State] -- initial states
           , Formula APType -> State -> Bool -- isFinal
           , State -> Maybe Input -> [State] -- deltaPush
           , State -> Maybe Input -> [State] -- deltaShift
           , State -> State -> [State] -- deltaPop
           , [Formula APType] -- closure
           )
makeOpa phi isOmega (sls, sprs) inputFilter =
  ( bitenc
  , prec
  , is
  , isFinal bitenc
  , deltaPush  as pcs scs pushRules  -- apply PushRules
  , deltaShift as pcs scs shiftRules -- apply ShiftRules
  , deltaPop   as pcs scs popRules   -- apply PopRules
  , cl
  )
  where
        -- remove double negations
        nphi = normalize phi
        -- APs in phi
        als = getProps nphi \\ sls
        -- all the APs which make up the language (L is in powerset(AP))
        tsprops = sls ++ als
        -- generate the powerset of AP, each time taking a prop from the structural list
        inputSet = filter (inputFilter bitenc) $ E.generateInputs bitenc sls als
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
        -- generate all possible stack obligations for the omega case
        scs = stackCombs bitenc cl
        -- generate initial states
        is = initials isOmega bitenc nphi cl as

        -- generate all delta rules of the OPA
        (shiftRules, pushRules, popRules) = deltaRules bitenc cl prec
        -- generate the deltaPush function (state and props are its parameters)
        deltaPush atoms pcombs scombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                                props Nothing Nothing
        -- generate the deltaShift function (state and props are its parameters)
        deltaShift atoms pcombs scombs rgroup state props = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                                props Nothing Nothing
        -- generate the deltaPop function (state and popped are its parameters)
        deltaPop atoms pcombs scombs rgroup state popped = fstates
          where fstates = delta rgroup atoms pcombs scombs state
                                Nothing (Just popped) Nothing
