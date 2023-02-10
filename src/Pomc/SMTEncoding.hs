{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{- |
   Module      : Pomc.SMTEncoding
   Copyright   : 2020-2022 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.SMTEncoding ( SMTResult(..)
                        , isSatisfiable
                        ) where

import Prelude hiding (take, pred)
import qualified Prelude as P
import Control.Exception (assert)
import Control.Monad (filterM)
-- import System.IO (stderr)

import Pomc.Prop (Prop(..))
import Pomc.Potl (Dir(..), Formula(..), pnf)
import Pomc.Prec (Prec(..), Alphabet, isComplete)

import qualified What4.Config as W4
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Solver as W4
import qualified What4.Protocol.SMTLib2 as W4

import GHC.TypeNats (type (<=))
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context hiding (take)
import qualified Data.Parameterized.NatRepr as NR

import Data.Bits (finiteBitSize, countLeadingZeros)
import qualified Data.BitVector.Sized as BV
import Data.Tuple (swap)
import Data.List ((\\))
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Data.Foldable (foldlM)

import qualified Debug.Trace as DBG

data SMTResult = Sat | Unsat | Unknown deriving (Eq, Show)

data TableauNode a = TableauNode { nodeGammaC :: [Formula a]
                                 , nodeSmb    :: Prop a
                                 , nodeStack  :: Integer
                                 , nodeCtx    :: Integer
                                 , nodeIdx    :: Integer
                                 } deriving Show
newtype SymEvalFn sym = SymEvalFn {
  symEval :: forall tp . W4.SymExpr sym tp -> IO (W4.GroundValue tp) }


z3executable :: FilePath
z3executable = "z3"

isSatisfiable :: (Ord a, Show a)
              => Alphabet a
              -> Formula a
              -> IO (SMTResult)
isSatisfiable alphabet phi = do
  Some ng <- newIONonceGenerator
  sym <- W4.newExprBuilder W4.FloatIEEERepr W4.EmptyExprBuilderState ng
  -- We use z3 for the time being, might try more backends later
  W4.extendConfig W4.z3Options (W4.getConfiguration sym)

  (fenc, modelQuery) <- encodeFormula sym alphabet (pnf phi)

  let logData = W4.defaultLogData -- { W4.logHandle = Just stderr }
  W4.withZ3 sym z3executable logData $ \session -> do
    -- Assume fenc is true
    W4.assume (W4.sessionWriter session) fenc
    W4.runCheckSat session $ \result ->
      case result of
        W4.Sat (gef, _) -> do
          tableau <- modelQuery (SymEvalFn $ W4.groundEval gef)
            (\pred -> do
                W4.assume (W4.sessionWriter session) pred
                W4.runCheckSat session $ \newResult ->
                  case newResult of
                    W4.Sat (newSef, _) -> return $ SymEvalFn $ W4.groundEval newSef
                    _ -> error "Unexpected unsat or unknown."
            ) 10
          DBG.traceShowM tableau
          return Sat
        W4.Unsat _ -> return Unsat
        W4.Unknown -> return Unknown

type SType w = W4.BaseBVType w
sRepr :: 1 <= w => BV.NatRepr w -> W4.BaseTypeRepr (W4.BaseBVType w)
sRepr = W4.BaseBVRepr

type NodeType nw = W4.BaseBVType nw
nodeRepr :: 1 <= nw => BV.NatRepr nw -> W4.BaseTypeRepr (W4.BaseBVType nw)
nodeRepr = W4.BaseBVRepr
type SymNode sym nw = W4.SymBV sym nw

type PrecFunType sym w = W4.SymFn sym (EmptyCtx ::> SType w ::> SType w) W4.BaseBoolType

encodeFormula :: forall a sym.
                 (Ord a, Show a, W4.IsSymExprBuilder sym)
              => sym
              -> Alphabet a
              -> Formula a
              -> IO (W4.Pred sym, SymEvalFn sym -> (W4.Pred sym -> IO (SymEvalFn sym)) -> Integer -> IO [TableauNode a])
encodeFormula sym alphabet phi = do
  let closLen = length clos
  Some bvWidth <- return $ NR.mkNatRepr $ toEnum
    $ finiteBitSize closLen - countLeadingZeros closLen
  Just NR.LeqProof <- return $ NR.isPosNat bvWidth
  let formulaIndices = assert (closLen < 2^(NR.intValue bvWidth))
        $ map (BV.mkBV bvWidth) [0..(toInteger closLen - 1)]
  formulaSyms <- mapM (W4.bvLit sym bvWidth) formulaIndices
  let formulaSymMap = Map.fromList $ zip clos formulaSyms
      formulaIdxMap = Map.fromList $ zip clos formulaIndices
  -- Uninterpreted Function Symbols
  let nbvw = NR.knownNat @5
  Just NR.LeqProof <- return $ NR.isPosNat nbvw
  gamma  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "Gamma")
            (Empty :> sRepr bvWidth :> (nodeRepr nbvw)) W4.BaseBoolRepr
  sigma  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "sigma")
            (Empty :> sRepr bvWidth) W4.BaseBoolRepr
  struct <- W4.freshTotalUninterpFn sym (W4.safeSymbol "struct") (nodeArgCtx nbvw) $ sRepr bvWidth
  smb    <- W4.freshTotalUninterpFn sym (W4.safeSymbol "smb") (nodeArgCtx nbvw) $ sRepr bvWidth
  yield  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "yield") (precArgCtx bvWidth) W4.BaseBoolRepr
  equal  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "equal") (precArgCtx bvWidth) W4.BaseBoolRepr
  take   <- W4.freshTotalUninterpFn sym (W4.safeSymbol "take") (precArgCtx bvWidth) W4.BaseBoolRepr
  stack  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "stack") (nodeArgCtx nbvw) (nodeRepr nbvw)
  ctx    <- W4.freshTotalUninterpFn sym (W4.safeSymbol "ctx") (nodeArgCtx nbvw) (nodeRepr nbvw)
  -- Encoding
  phiAxioms <- makePhiAxioms bvWidth nbvw sigma struct smb formulaSymMap
  phiOPM <- makePhiOPM yield equal take formulaSymMap

  -- xnf(φ)(0)
  sym0 <- W4.bvLit sym nbvw $ BV.mkBV nbvw 0
  xnfPhi0 <- groundxnf formulaSymMap gamma (xnf phi) sym0

  -- smb(0) = #
  smb0 <- W4.applySymFn sym smb (Empty :> sym0)
  smb0EqEnd <- W4.bvEq sym smb0 (formulaSymMap Map.! (Atomic End))

  -- stack(0) = 0
  stack0 <- W4.applySymFn sym stack (Empty :> sym0)
  stack0Eq0 <- W4.bvEq sym stack0 sym0

  -- ctx(0) = 0
  ctx0 <- W4.applySymFn sym ctx (Empty :> sym0)
  ctx0Eq0 <- W4.bvEq sym ctx0 sym0

  -- ∀x (...)
  xSym <- W4.freshBoundVar sym (W4.safeSymbol "x") (nodeRepr nbvw)
  let xExpr = W4.varExpr sym xSym
  kExpr <- W4.freshConstant sym (W4.safeSymbol "k") (nodeRepr nbvw)
  -- x < k
  xltk <- W4.bvUlt sym xExpr kExpr

  endx <- endTerm formulaSymMap gamma xExpr
  conflictx <- conflict bvWidth sigma gamma xExpr
  pnextx <- pnext nbvw formulaSymMap gamma struct yield take xExpr
  -- push(x) → PUSH(x)
  checkPushx <- checkPrec smb struct yield xExpr
  pushx <- push nbvw formulaSymMap gamma smb struct stack ctx yield equal take xExpr
  pushxImpliesPushx <- W4.impliesPred sym checkPushx pushx
  -- shift(x) → SHIFT(x)
  checkShiftx <- checkPrec smb struct equal xExpr
  shiftx <- shift nbvw formulaSymMap gamma smb struct stack ctx xExpr
  shiftxImpliesShiftx <- W4.impliesPred sym checkShiftx shiftx
  -- pop(x) → POP(x)
  checkPopx <- checkPrec smb struct take xExpr
  popx <- pop bvWidth nbvw gamma smb stack ctx xExpr
  popxImpliesPopx <- W4.impliesPred sym checkPopx popx

  quantifiedAnd <- bigAndPred sym [ endx, conflictx, pnextx
                                  , pushxImpliesPushx
                                  , shiftxImpliesShiftx
                                  , popxImpliesPopx
                                  ]
  quantifiedImplies <- W4.impliesPred sym xltk quantifiedAnd
  forallx <- W4.forallPred sym xSym quantifiedImplies

  unravelPhik <- bigAndPred sym [ phiAxioms, phiOPM
                                , xnfPhi0, smb0EqEnd, stack0Eq0, ctx0Eq0
                                , forallx
                                ]

  emptyk <- emptyTerm nbvw formulaSymMap gamma stack kExpr
  kgt0 <- W4.bvUlt sym sym0 kExpr
  -- kltn <- W4.intLit sym 10 >>= W4.intLt sym kExpr
  -- keqn <- W4.intLit sym 2 >>= W4.intEq sym kExpr
  existsk <- bigAndPred sym [kgt0, unravelPhik, emptyk]
  -- kExpr is implicitly existentially quantified
  return (existsk, queryTableau sym formulaSymMap formulaIdxMap bvWidth nbvw gamma smb stack ctx kExpr)
  where
    nodeArgCtx :: 1 <= nw
               => NR.NatRepr nw
               -> Assignment W4.BaseTypeRepr (EmptyCtx ::> NodeType nw)
    nodeArgCtx nbvw = Empty :> nodeRepr nbvw

    precArgCtx :: 1 <= w
               => NR.NatRepr w
               -> Assignment W4.BaseTypeRepr (EmptyCtx ::> SType w ::> SType w)
    precArgCtx bvWidth = Empty :> sRepr bvWidth :> sRepr bvWidth

    (structClos, clos) = closure alphabet phi

    -- φ_axioms
    makePhiAxioms :: (1 <= w, 1 <= nw)
                  => BV.NatRepr w
                  -> BV.NatRepr nw
                  -> W4.SymFn sym (EmptyCtx ::> SType w) W4.BaseBoolType
                  -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
                  -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
                  -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
                  -> IO (W4.Pred sym)
    makePhiAxioms bvWidth nbvw sigma struct smb formulaSymMap = do
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- bigAnd sym (W4.applySymFn sym sigma . (Empty :>))
        $ map (formulaSymMap Map.!) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- bigAnd sym
        (\p -> W4.applySymFn sym sigma (Empty :> p) >>= W4.notPred sym)
        $ map (formulaSymMap Map.!) (clos \\ structClos)
      -- Needed because we use BitVectors for S
      -- ySym <- W4.freshBoundVar sym (W4.safeSymbol "y") $ sRepr bvWidth
      -- let yExpr = W4.varExpr sym ySym
      -- sigmaY <- W4.applySymFn sym sigma (Empty :> yExpr)
      -- maxSLit <- W4.bvLit sym bvWidth $ BV.mkBV bvWidth $ toInteger $ Map.size formulaSymMap
      -- yLeqMaxSLit <- W4.bvUle sym yExpr maxSLit
      -- sigmaYImpl <- W4.impliesPred sym sigmaY yLeqMaxSLit
      -- onlyFormulasInSigma <- W4.forallPred sym ySym sigmaYImpl
      -- Another way of doing it
      onlyFormulasInSigma <- bigAnd sym
        (\p -> do
            pLit <- W4.bvLit sym bvWidth $ BV.mkBV bvWidth p
            sigmaP <- W4.applySymFn sym sigma (Empty :> pLit)
            W4.notPred sym sigmaP)
        [(toInteger $ Map.size formulaSymMap)..(2^(NR.intValue bvWidth) - 1)]
      -- ∀x(Σ(struct(x)) ∧ Σ(smb(x)))
      xSym         <- W4.freshBoundVar sym (W4.safeSymbol "x") (nodeRepr nbvw)
      structX      <- W4.applySymFn sym struct (Empty :> W4.varExpr sym xSym)
      sigmaStructX <- W4.applySymFn sym sigma  (Empty :> structX)
      smbX         <- W4.applySymFn sym smb    (Empty :> W4.varExpr sym xSym)
      sigmaSmbX    <- W4.applySymFn sym sigma  (Empty :> smbX)
      forallArg    <- W4.andPred sym sigmaStructX sigmaSmbX
      assertForall <- W4.forallPred sym xSym forallArg

      bigAndPred sym [allStructInSigma, allOtherNotInSigma, assertForall, onlyFormulasInSigma]

    -- φ_OPM -- Assumes (snd $ alphabet) is a complete OPM
    makePhiOPM :: PrecFunType sym w
               -> PrecFunType sym w
               -> PrecFunType sym w
               -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
               -> IO (W4.Pred sym)
    makePhiOPM yield equal take formulaSymMap = assert (isComplete alphabet)
      $ bigAnd sym assertPrecPair
      $ snd alphabet ++ [(End, p, Yield) | p <- fst alphabet] ++ [(End, End, Equal)]
      where assertPrecPair (p, q, prec) = do
              let pqArg = Empty
                          :> (formulaSymMap Map.! Atomic p)
                          :> (formulaSymMap Map.! Atomic q)
                  (nPrec1, nPrec2) = getNegPrec prec
              posPrec  <- W4.applySymFn sym (getPosPrec prec) pqArg
              negPrec1 <- W4.applySymFn sym nPrec1 pqArg >>= W4.notPred sym
              negPrec2 <- W4.applySymFn sym nPrec2 pqArg >>= W4.notPred sym
              bigAndPred sym [posPrec, negPrec1, negPrec2]

            getPosPrec Yield = yield
            getPosPrec Equal = equal
            getPosPrec Take = take

            getNegPrec Yield = (equal, take)
            getNegPrec Equal = (yield, take)
            getNegPrec Take = (yield, equal)

    -- push(xExpr), shift(xExpr), pop(xExpr)
    checkPrec :: W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
              -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
              -> PrecFunType sym w
              -> SymNode sym nw
              -> IO (W4.SymExpr sym W4.BaseBoolType)
    checkPrec smb struct precRel xExpr = do
      smbX <- W4.applySymFn sym smb (Empty :> xExpr)
      structX <- W4.applySymFn sym struct (Empty :> xExpr)
      W4.applySymFn sym precRel (Empty :> smbX :> structX)

    -- xnf(f)_G(xExpr)
    groundxnf :: Map.Map (Formula a) (W4.SymExpr sym (SType w))
              -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
              -> Formula a
              -> SymNode sym nw
              -> IO (W4.Pred sym)
    groundxnf fsm gamma f xExpr = case f of
      T                -> return $ W4.truePred sym
      Atomic _         -> applyGamma f
      Not T            -> return $ W4.falsePred sym
      Not g@(Atomic _) -> applyGamma g >>= W4.notPred sym
      Not _            -> error "Supplied formula is not in Positive Normal Form."
      Or g h           -> boolPred W4.orPred g h
      And g h          -> boolPred W4.andPred g h
      Xor g h          -> boolPred W4.xorPred g h
      Implies g h      -> boolPred (\s glhs grhs -> do
                                       nglhs <- W4.notPred s glhs
                                       W4.orPred s nglhs grhs) g h
      Iff g h          -> boolPred W4.eqPred g h
      PNext _ _        -> applyGamma f
      PBack _ _        -> error "Past operators not supported yet."
      WPNext _ _       -> applyGamma f
      XNext _ _        -> applyGamma f
      XBack _ _        -> error "Past operators not supported yet."
      WXNext _ _       -> applyGamma f
      HNext _ _        -> error "Hierarchical operators not supported yet."
      HBack _ _        -> error "Hierarchical operators not supported yet."
      Until _ _ _      -> error "Supplied formula is not in Next Normal Form."
      Release _ _ _    -> error "Supplied formula is not in Next Normal Form."
      Since _ _ _      -> error "Past operators not supported yet."
      HUntil _ _ _     -> error "Hierarchical operators not supported yet."
      HSince _ _ _     -> error "Hierarchical operators not supported yet."
      Eventually _     -> error "LTL operators not supported yet."
      Always _         -> error "LTL operators not supported yet."
      AuxBack _ _      -> error "AuxBack not supported in SMT encoding."
      where boolPred op lhs rhs = do
              glhs <- groundxnf fsm gamma lhs xExpr
              grhs <- groundxnf fsm gamma rhs xExpr
              op sym glhs grhs

            applyGamma g = W4.applySymFn sym gamma
              (Empty :> (fsm Map.! g) :> xExpr)

    -- PUSH(xExpr)
    push :: (1 <= w, 1 <= nw)
         => NR.NatRepr nw
         -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
         -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
         -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
         -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
         -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
         -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
         -> PrecFunType sym w
         -> PrecFunType sym w
         -> PrecFunType sym w
         -> SymNode sym nw
         -> IO (W4.Pred sym)
    push nbvw formulaSymMap gamma smb struct stack ctx yield equal take xExpr = do
      let ioxp1 = W4.bvLit sym nbvw (BV.mkBV nbvw 1) >>= W4.bvAdd sym xExpr
          propagateNext (next, arg) = do
            lhs <- W4.applySymFn sym gamma (Empty :> (formulaSymMap Map.! next) :> xExpr)
            rhs <- ioxp1 >>= groundxnf formulaSymMap gamma (xnf arg)
            W4.eqPred sym lhs rhs
      -- big ands
      pnextRule <- bigAnd sym propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- bigAnd sym propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      xp1 <- ioxp1
      smbxp1 <- W4.applySymFn sym smb (Empty :> xp1)
      structx <- W4.applySymFn sym struct (Empty :> xExpr)
      smbRule <- W4.bvEq sym smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackRule <- W4.bvEq sym stackxp1 xExpr
      -- stack(x) = 0 → ctx(x + 1) = 0
      sym0 <- W4.bvLit sym nbvw (BV.mkBV nbvw 0)
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      stackxEq0 <- W4.bvEq sym stackx sym0
      ctxxp1Eq0 <- W4.bvEq sym ctxxp1 sym0
      rootCtxRule <- W4.impliesPred sym stackxEq0 ctxxp1Eq0
      -- (stack(x) != 0 ∧ (push(x − 1) ∨ shift(x − 1))) → ctx(x + 1) = x − 1
      stackxNeq0 <- W4.bvEq sym stackx sym0 >>= W4.notPred sym
      sym1 <- W4.bvLit sym nbvw (BV.mkBV nbvw 1)
      xm1 <- W4.bvSub sym xExpr sym1
      pushxm1 <- checkPrec smb struct yield xm1
      shiftxm1 <- checkPrec smb struct equal xm1
      pushOrShiftxm1 <- W4.orPred sym pushxm1 shiftxm1
      stackxNeq0AndpushOrShiftxm1 <- W4.andPred sym stackxNeq0 pushOrShiftxm1
      ctxxp1Eqxm1 <- W4.bvEq sym ctxxp1 xm1
      pushShiftCtxRule <- W4.impliesPred sym stackxNeq0AndpushOrShiftxm1 ctxxp1Eqxm1
      -- (stack(x) != 0 ∧ pop(x − 1)) → ctx(x + 1) = ctx(x)
      popxm1 <- checkPrec smb struct take xm1
      stackxNeq0AndPopxm1 <- W4.andPred sym stackxNeq0 popxm1
      ctxx <- W4.applySymFn sym ctx (Empty :> xExpr)
      ctxxp1Eqctxx <- W4.bvEq sym ctxxp1 ctxx
      popCtxRule <- W4.impliesPred sym stackxNeq0AndPopxm1 ctxxp1Eqctxx
      -- Final and
      bigAndPred sym [ pnextRule, wpnextRule
                     , smbRule, stackRule
                     , rootCtxRule, pushShiftCtxRule, popCtxRule
                     ]

    -- SHIFT(xExpr)
    shift :: (1 <= w, 1 <= nw)
          => NR.NatRepr nw
          -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
          -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
          -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
          -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
          -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
          -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
          -> SymNode sym nw
          -> IO (W4.Pred sym)
    shift nbvw formulaSymMap gamma smb struct stack ctx xExpr = do
      let ioxp1 = W4.bvLit sym nbvw (BV.mkBV nbvw 1) >>= W4.bvAdd sym xExpr
          propagateNext (next, arg) = do
            lhs <- W4.applySymFn sym gamma (Empty :> (formulaSymMap Map.! next) :> xExpr)
            rhs <- ioxp1 >>= groundxnf formulaSymMap gamma (xnf arg)
            W4.impliesPred sym lhs rhs
      -- big ands
      pnextRule <- bigAnd sym propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- bigAnd sym propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      xp1 <- ioxp1
      smbxp1 <- W4.applySymFn sym smb (Empty :> xp1)
      structx <- W4.applySymFn sym struct (Empty :> xExpr)
      smbRule <- W4.bvEq sym smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      stackRule <- W4.bvEq sym stackxp1 stackx
      -- ctx(x + 1) = ctx(x)
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      ctxx <- W4.applySymFn sym ctx (Empty :> xExpr)
      ctxRule <- W4.bvEq sym ctxxp1 ctxx
      -- Final and
      bigAndPred sym [pnextRule, wpnextRule, smbRule, stackRule, ctxRule]

    -- POP(xExpr)
    pop :: (1 <= w, 1 <= nw)
        => BV.NatRepr w
        -> BV.NatRepr nw
        -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
        -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
        -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
        -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
        -> SymNode sym nw
        -> IO (W4.Pred sym)
    pop bvWidth nbvw gamma smb stack ctx xExpr = do
      xp1 <- W4.bvLit sym nbvw (BV.mkBV nbvw 1) >>= W4.bvAdd sym xExpr
      -- ∀p(Γ(p, x) ↔ Γ(p, x + 1))
      pSym <- W4.freshBoundVar sym (W4.safeSymbol "p") $ sRepr bvWidth
      let pExpr = W4.varExpr sym pSym
      gammapx <- W4.applySymFn sym gamma (Empty :> pExpr :> xExpr)
      gammapxp1 <- W4.applySymFn sym gamma (Empty :> pExpr :> xp1)
      gammaIff <- W4.eqPred sym gammapx gammapxp1
      gammaRule <- W4.forallPred sym pSym gammaIff
      -- smb(x + 1) = smb(stack(x))
      smbxp1 <- W4.applySymFn sym smb (Empty :> xp1)
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      smbstackx <- W4.applySymFn sym smb (Empty :> stackx)
      smbRule <- W4.bvEq sym smbxp1 smbstackx
      -- stack(x + 1) = stack(stack(x))
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackstackx <- W4.applySymFn sym stack (Empty :> stackx)
      stackRule <- W4.bvEq sym stackxp1 stackstackx
      -- ctx(x + 1) = ctx(stack(x))
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      ctxstackx <- W4.applySymFn sym ctx (Empty :> stackx)
      ctxRule <- W4.bvEq sym ctxxp1 ctxstackx
      -- Final and
      bigAndPred sym [gammaRule, smbRule, stackRule, ctxRule]

    -- END(xExpr)
    endTerm :: Map.Map (Formula a) (W4.SymExpr sym (SType w))
            -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
            -> SymNode sym nw
            -> IO (W4.Pred sym)
    endTerm fsm gamma xExpr = do
      let noGamma g = W4.applySymFn sym gamma (Empty :> (fsm Map.! g) :> xExpr)
                      >>= W4.notPred sym
      -- Γ(#, x)
      gammaEndx <- W4.applySymFn sym gamma (Empty :> (fsm Map.! Atomic End) :> xExpr)
      -- ∧_(PNext t α ∈ Cl(φ)) ¬Γ((PNext t α)_G, x)
      noGammaPNext <- bigAnd sym noGamma [g | g@(PNext _ _) <- clos]
      -- ∧_(p ∈ AP) ¬Γ(p, x)
      noGammaAP <- bigAnd sym noGamma [g | g@(Atomic (Prop _)) <- clos]
      noGammaPNextAndnoGammaAP <- W4.andPred sym noGammaPNext noGammaAP
      -- Final →
      W4.impliesPred sym gammaEndx noGammaPNextAndnoGammaAP

    -- CONFLICT(xExpr)
    conflict :: 1 <= w
             => BV.NatRepr w
             -> W4.SymFn sym (EmptyCtx ::> SType w) W4.BaseBoolType
             -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
             -> SymNode sym nw
             -> IO (W4.Pred sym)
    conflict bvWidth sigma gamma xExpr = do
      pSym <- W4.freshBoundVar sym (W4.safeSymbol "p") $ sRepr bvWidth
      qSym <- W4.freshBoundVar sym (W4.safeSymbol "q") $ sRepr bvWidth
      let pExpr = W4.varExpr sym pSym
          qExpr = W4.varExpr sym qSym
      sigmap <- W4.applySymFn sym sigma (Empty :> pExpr)
      sigmaq <- W4.applySymFn sym sigma (Empty :> qExpr)
      gammapx <- W4.applySymFn sym gamma (Empty :> pExpr :> xExpr)
      gammaqx <- W4.applySymFn sym gamma (Empty :> qExpr :> xExpr)
      andAll <- bigAndPred sym [sigmap, sigmaq, gammapx, gammaqx]
      pEqq <- W4.bvEq sym pExpr qExpr
      pqImpl <- W4.impliesPred sym andAll pEqq
      forallq <- W4.forallPred sym qSym pqImpl
      W4.forallPred sym pSym forallq

    -- PNEXT(xExpr)
    pnext :: 1 <= nw
          => BV.NatRepr nw
          -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
          -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
          -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
          -> PrecFunType sym w
          -> PrecFunType sym w
          -> SymNode sym nw
          -> IO (W4.Pred sym)
    pnext nbvw fsm gamma struct yield take xExpr = do
      let pnextPrec prec g = do
            -- Γ(g, x)
            gammagx <- W4.applySymFn sym gamma (Empty :> (fsm Map.! g) :> xExpr)
            -- struct(x) prec struct(x + 1)
            structx <- W4.applySymFn sym struct (Empty :> xExpr)
            xp1 <- W4.bvLit sym nbvw (BV.mkBV nbvw 1) >>= W4.bvAdd sym xExpr
            structxp1 <- W4.applySymFn sym struct (Empty :> xp1)
            structPrec <- W4.applySymFn sym prec (Empty :> structx :> structxp1)
            -- Final negated and
            andGammagxStructPrec <- W4.andPred sym gammagx structPrec
            W4.notPred sym andGammagxStructPrec
      -- ∧_(PNext d α ∈ Cl(φ)) (...)
      pnextDown <- bigAnd sym (pnextPrec take) [g | g@(PNext Down _) <- clos]
      -- ∧_(PNext u α ∈ Cl(φ)) (...)
      pnextUp <- bigAnd sym (pnextPrec yield) [g | g@(PNext Up _) <- clos]
      W4.andPred sym pnextDown pnextUp

    -- EMPTY(xExpr)
    emptyTerm :: 1 <= nw
              => NR.NatRepr nw
              -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
              -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
              -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
              -> SymNode sym nw
              -> IO (W4.Pred sym)
    emptyTerm nbvw fsm gamma stack xExpr = do
      -- Γ(#, x)
      gammaEndx <- W4.applySymFn sym gamma (Empty :> (fsm Map.! Atomic End) :> xExpr)
      -- stack(x) = 0
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      sym0 <- W4.bvLit sym nbvw $ BV.mkBV nbvw 0
      stackxEq0 <- W4.bvEq sym stackx sym0
      W4.andPred sym gammaEndx stackxEq0


closure :: Ord a => Alphabet a -> Formula a -> ([Formula a], [Formula a])
closure alphabet phi = (structClos, Set.toList . Set.fromList $ structClos ++ closList phi)
  where
    structClos = map Atomic $ End : (fst alphabet)
    closList f =
      case f of
        T                -> []
        Atomic _         -> [f]
        Not T            -> []
        Not g@(Atomic _) -> [g]
        Not _            -> error "Supplied formula is not in Positive Normal Form."
        Or g h           -> closList g ++ closList h
        And g h          -> closList g ++ closList h
        Xor g h          -> closList g ++ closList h
        Implies g h      -> closList g ++ closList h
        Iff g h          -> closList g ++ closList h
        PNext _ g        -> f : closList g
        PBack _ _        -> error "Past operators not supported yet."
        WPNext _ g       -> f : closList g
        XNext _ g        -> f : closList g
        XBack _ _        -> error "Past operators not supported yet."
        WXNext _ g       -> f : closList g
        HNext _ _        -> error "Hierarchical operators not supported yet."
        HBack _ _        -> error "Hierarchical operators not supported yet."
        Until dir g h    -> [f, PNext dir f, XNext dir f] ++ closList g ++ closList h
        Release dir g h  -> [f, WPNext dir f, WXNext dir f] ++ closList g ++ closList h
        Since _ _ _      -> error "Past operators not supported yet."
        HUntil _ _ _     -> error "Hierarchical operators not supported yet."
        HSince _ _ _     -> error "Hierarchical operators not supported yet."
        Eventually _     -> error "LTL operators not supported yet."
        Always _         -> error "LTL operators not supported yet."
        AuxBack _ _      -> error "AuxBack not supported in SMT encoding."

xnf :: Formula a -> Formula a
xnf f = case f of
  T               -> f
  Atomic _        -> f
  Not T           -> f
  Not (Atomic _)  -> f
  Not _           -> error "Supplied formula is not in Positive Normal Form."
  Or g h          -> Or (xnf g) (xnf h)
  And g h         -> And (xnf g) (xnf h)
  Xor g h         -> Xor (xnf g) (xnf h)
  Implies g h     -> Implies (xnf g) (xnf h)
  Iff g h         -> Iff (xnf g) (xnf h)
  PNext _ _       -> f
  PBack _ _       -> error "Past operators not supported yet."
  WPNext _ _      -> f
  XNext _ _       -> f
  XBack _ _       -> error "Past operators not supported yet."
  WXNext _ _      -> f
  HNext _ _       -> error "Hierarchical operators not supported yet."
  HBack _ _       -> error "Hierarchical operators not supported yet."
  Until dir g h   -> xnf h `Or` (xnf g `And` (PNext dir f `Or` XNext dir f))
  Release dir g h -> xnf h `And` (xnf g `Or` (WPNext dir f `And` WXNext dir f))
  Since _ _ _     -> error "Past operators not supported yet."
  HUntil _ _ _    -> error "Hierarchical operators not supported yet."
  HSince _ _ _    -> error "Hierarchical operators not supported yet."
  Eventually _    -> error "LTL operators not supported yet."
  Always _        -> error "LTL operators not supported yet."
  AuxBack _ _     -> error "AuxBack not supported in SMT encoding."

bigAnd :: W4.IsExprBuilder t => t -> (a -> IO (W4.Pred t)) -> [a] -> IO (W4.Pred t)
bigAnd sym predGen items =
  foldlM (\conj x -> predGen x >>= W4.andPred sym conj) (W4.truePred sym) items

bigAndPred :: W4.IsExprBuilder t => t -> [W4.Pred t] -> IO (W4.Pred t)
bigAndPred sym = bigAnd sym (id . return)

queryTableau :: forall a sym w nw. (Show a, Ord a, W4.IsSymExprBuilder sym, 1 <= w, 1 <= nw)
             => sym
             -> Map.Map (Formula a) (W4.SymExpr sym (SType w))
             -> Map.Map (Formula a) (BV.BV w)
             -> NR.NatRepr w
             -> NR.NatRepr nw
             -> W4.SymFn sym (EmptyCtx ::> SType w ::> NodeType nw) W4.BaseBoolType
             -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (SType w)
             -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
             -> W4.SymFn sym (EmptyCtx ::> NodeType nw) (NodeType nw)
             -> SymNode sym nw
             -> SymEvalFn sym
             -> (W4.Pred sym -> IO (SymEvalFn sym))
             -> Integer
             -> IO [TableauNode a]
queryTableau sym fsm fim bvWidth nbvw gamma smb stack ctx kExpr sef solver maxLen = do
  traceLen <- fmap BV.asUnsigned $ symEval sef kExpr
  let unrollLen = min traceLen maxLen
  nodeQueries <- mapM queryTableauNode [0..unrollLen]
  let (preds, evalQueries) = P.unzip nodeQueries
  queryPred <- bigAndPred sym preds
  newSef <- solver queryPred
  mapM ($ newSef) evalQueries
  where queryTableauNode :: Integer -> IO (W4.Pred sym, SymEvalFn sym -> IO (TableauNode a))
        queryTableauNode idx = do
          idxExpr <- W4.bvLit sym nbvw $ BV.mkBV nbvw idx
          let mkGammaConst (f, fSym) = do
                gammaConst <- W4.freshConstant sym
                              (W4.safeSymbol $ "gamma_" ++ show (fim Map.! f) ++ show idx)
                              W4.BaseBoolRepr
                return (f, fSym, gammaConst)
              mkGammaPred (_, fSym, gammaConst) = do
                gammaApply <- W4.applySymFn sym gamma (Empty :> fSym :> idxExpr)
                W4.eqPred sym gammaConst gammaApply
          gammaConsts <- mapM mkGammaConst $ Map.toList fsm
          gammaPreds <- bigAnd sym mkGammaPred gammaConsts
          smbConst <- W4.freshConstant sym (W4.safeSymbol $ "smb_" ++ show idx) $ sRepr bvWidth
          smbApply <- W4.applySymFn sym smb (Empty :> idxExpr)
          smbPred <- W4.bvEq sym smbConst smbApply
          stackConst <- W4.freshConstant sym (W4.safeSymbol $ "stack_" ++ show idx) (nodeRepr nbvw)
          stackApply <- W4.applySymFn sym stack (Empty :> idxExpr)
          stackPred <- W4.bvEq sym stackConst stackApply
          ctxConst <- W4.freshConstant sym (W4.safeSymbol $ "ctx_" ++ show idx) (nodeRepr nbvw)
          ctxApply <- W4.applySymFn sym ctx (Empty :> idxExpr)
          ctxPred <- W4.bvEq sym ctxConst ctxApply
          allPreds <- bigAndPred sym [smbPred, stackPred, ctxPred, gammaPreds]
          let doQuery newSef = do
                smbVal <- symEval newSef smbConst
                let idxFormulaMap = Map.fromList $ map swap $ Map.toList fim
                    Atomic smbProp = idxFormulaMap Map.! smbVal
                stackVal <- symEval newSef stackConst
                ctxVal <- symEval newSef ctxConst
                gammaVals <- filterM (\(_, _, gammaConst) -> symEval newSef gammaConst) gammaConsts
                return TableauNode { nodeGammaC = map (\(f, _, _) -> f) gammaVals
                                   , nodeSmb = smbProp
                                   , nodeStack = BV.asUnsigned stackVal
                                   , nodeCtx = BV.asUnsigned ctxVal
                                   , nodeIdx = idx
                                   }
          return (allPreds, doQuery)
