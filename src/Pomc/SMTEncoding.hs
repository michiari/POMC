{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
   Module      : Pomc.SMTEncoding
   Copyright   : 2020-2022 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.SMTEncoding ( SMTResult(..)
                        , isSatisfiable
                        ) where

import Prelude hiding (take)

import Pomc.Prop (Prop(..))
import Pomc.Potl (Dir(..), Formula(..), pnf)
import Pomc.Prec (Prec(..), Alphabet)

-- import System.IO (FilePath)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context hiding (take)

import What4.Config (extendConfig)
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Concrete as W4
import What4.Solver (defaultLogData, z3Options, withZ3)
import qualified What4.Solver as W4
import What4.Protocol.SMTLib2 (assume, sessionWriter, runCheckSat)

import Data.List ((\\))
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Data.Foldable (foldlM)

-- import qualified Debug.Trace as DBG

data SMTResult = Sat | Unsat | Unknown deriving (Eq, Show)

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
  extendConfig z3Options (W4.getConfiguration sym)

  fenc <- encodeFormula sym alphabet (pnf phi)

  withZ3 sym z3executable defaultLogData $ \session -> do
    -- Assume fenc is true
    assume (sessionWriter session) fenc
    runCheckSat session $ \result ->
      case result of
        W4.Sat _ -> return Sat
        W4.Unsat _ -> return Unsat
        W4.Unknown -> return Unknown

type SType = W4.BaseIntegerType
sRepr :: W4.BaseTypeRepr W4.BaseIntegerType
sRepr = W4.BaseIntegerRepr

type NodeType = W4.BaseIntegerType
nodeRepr :: W4.BaseTypeRepr W4.BaseIntegerType
nodeRepr = W4.BaseIntegerRepr
type SymNode sym = W4.SymInteger sym

type PrecFunType sym = W4.SymFn sym (EmptyCtx ::> SType ::> SType) W4.BaseBoolType

encodeFormula :: forall a sym.
                 (Ord a, Show a, W4.IsSymExprBuilder sym)
              => sym
              -> Alphabet a
              -> Formula a
              -> IO (W4.Pred sym)
encodeFormula sym alphabet phi = do
  formulaSyms <- mapM (W4.concreteToSym sym . W4.ConcreteInteger) [0..(toInteger $ length clos)]
  let formulaSymMap = Map.fromList $ zip clos formulaSyms
  -- Uninterpreted Function Symbols
  gamma  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "Gamma") gammaArgCtx W4.BaseBoolRepr
  sigma  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "sigma") sigmaArgCtx W4.BaseBoolRepr
  struct <- W4.freshTotalUninterpFn sym (W4.safeSymbol "struct") nodeArgCtx sRepr
  smb    <- W4.freshTotalUninterpFn sym (W4.safeSymbol "smb") nodeArgCtx sRepr
  yield  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "yield") precArgCtx W4.BaseBoolRepr
  equal  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "equal") precArgCtx W4.BaseBoolRepr
  take   <- W4.freshTotalUninterpFn sym (W4.safeSymbol "take") precArgCtx W4.BaseBoolRepr
  stack  <- W4.freshTotalUninterpFn sym (W4.safeSymbol "stack") nodeArgCtx nodeRepr
  ctx    <- W4.freshTotalUninterpFn sym (W4.safeSymbol "ctx") nodeArgCtx nodeRepr
  -- Encoding
  phiAxioms <- makePhiAxioms sigma struct smb formulaSymMap
  phiOPM <- makePhiOPM yield equal take formulaSymMap

  -- xnf(φ)(0)
  sym0 <- W4.intLit sym 0
  xnfPhi0 <- groundxnf formulaSymMap gamma (xnf phi) sym0

  -- smb(0) = #
  smb0 <- W4.applySymFn sym smb (Empty :> sym0)
  smb0EqEnd <- W4.intEq sym smb0 (formulaSymMap Map.! (Atomic End))

  -- ∀x (...)
  xSym <- W4.freshBoundVar sym (W4.safeSymbol "x") nodeRepr
  kSym <- W4.freshBoundVar sym (W4.safeSymbol "k") nodeRepr
  let xExpr = W4.varExpr sym xSym
      kExpr = W4.varExpr sym kSym
  -- x < k
  xltk <- W4.intLt sym xExpr kExpr

  endx <- endTerm formulaSymMap gamma xExpr
  conflictx <- conflict sigma gamma xExpr
  pnextx <- pnext formulaSymMap gamma struct yield take xExpr
  -- push(x) → PUSH(x)
  checkPushx <- checkPrec smb struct yield xExpr
  pushx <- push formulaSymMap gamma smb struct stack ctx yield equal take xExpr
  pushxImpliesPushx <- W4.impliesPred sym checkPushx pushx
  -- shift(x) → SHIFT(x)
  checkShiftx <- checkPrec smb struct equal xExpr
  shiftx <- shift formulaSymMap gamma smb struct stack ctx xExpr
  shiftxImpliesShiftx <- W4.impliesPred sym checkShiftx shiftx
  -- pop(x) → POP(x)
  checkPopx <- checkPrec smb struct take xExpr
  popx <- pop gamma smb stack ctx xExpr
  popxImpliesPopx <- W4.impliesPred sym checkPopx popx

  quantifiedAnd <- bigAndPred sym [ endx, conflictx, pnextx
                                  , pushxImpliesPushx
                                  , shiftxImpliesShiftx
                                  , popxImpliesPopx
                                  ]
  quantifiedImplies <- W4.impliesPred sym xltk quantifiedAnd
  forallx <- W4.forallPred sym xSym quantifiedImplies

  unravelPhik <- bigAndPred sym [phiAxioms, phiOPM, xnfPhi0, smb0EqEnd, forallx]

  emptyk <- emptyTerm formulaSymMap gamma stack kExpr
  kgt0 <- W4.intLt sym sym0 kExpr
  outerAnd <- bigAndPred sym [kgt0, unravelPhik, emptyk]
  W4.existsPred sym kSym outerAnd
  where
    gammaArgCtx :: Assignment W4.BaseTypeRepr (EmptyCtx ::> SType ::> NodeType)
    gammaArgCtx = W4.knownRepr

    sigmaArgCtx :: Assignment W4.BaseTypeRepr (EmptyCtx ::> SType)
    sigmaArgCtx = W4.knownRepr

    nodeArgCtx :: Assignment W4.BaseTypeRepr (EmptyCtx ::> NodeType)
    nodeArgCtx = W4.knownRepr

    precArgCtx :: Assignment W4.BaseTypeRepr (EmptyCtx ::> SType ::> SType)
    precArgCtx = W4.knownRepr

    (structClos, clos) = closure alphabet phi

    -- φ_axioms
    makePhiAxioms :: W4.SymFn sym (EmptyCtx ::> SType) W4.BaseBoolType
                  -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
                  -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
                  -> Map.Map (Formula a) (W4.SymExpr sym SType)
                  -> IO (W4.Pred sym)
    makePhiAxioms sigma struct smb formulaSymMap = do
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- bigAnd sym (W4.applySymFn sym sigma . (Empty :>))
        $ map (formulaSymMap Map.!) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- bigAnd sym
        (\p -> W4.applySymFn sym sigma (Empty :> p) >>= W4.notPred sym)
        $ map (formulaSymMap Map.!) (clos \\ structClos)
      -- ∀x(Σ(struct(x)) ∧ Σ(smb(x)))
      xSym         <- W4.freshBoundVar sym (W4.safeSymbol "x") nodeRepr
      structX      <- W4.applySymFn sym struct (Empty :> W4.varExpr sym xSym)
      sigmaStructX <- W4.applySymFn sym sigma  (Empty :> structX)
      smbX         <- W4.applySymFn sym smb    (Empty :> W4.varExpr sym xSym)
      sigmaSmbX    <- W4.applySymFn sym sigma  (Empty :> smbX)
      forallArg    <- W4.andPred sym sigmaStructX sigmaSmbX
      assertForall <- W4.forallPred sym xSym forallArg

      bigAndPred sym [allStructInSigma, allOtherNotInSigma, assertForall]

    -- φ_OPM -- Assumes (snd $ alphabet) is a complete OPM
    makePhiOPM :: PrecFunType sym
               -> PrecFunType sym
               -> PrecFunType sym
               -> Map.Map (Formula a) (W4.SymExpr sym SType)
               -> IO (W4.Pred sym)
    makePhiOPM yield equal take formulaSymMap =
      bigAnd sym assertPrecPair $ snd alphabet
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
    checkPrec :: W4.SymFn sym (EmptyCtx ::> NodeType) SType
              -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
              -> PrecFunType sym
              -> SymNode sym
              -> IO (W4.SymExpr sym W4.BaseBoolType)
    checkPrec smb struct precRel xExpr = do
      smbX <- W4.applySymFn sym smb (Empty :> xExpr)
      structX <- W4.applySymFn sym struct (Empty :> xExpr)
      W4.applySymFn sym precRel (Empty :> smbX :> structX)

    -- xnf(f)_G(xExpr)
    groundxnf :: Map.Map (Formula a) (W4.SymExpr sym SType)
              -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
              -> Formula a
              -> SymNode sym
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
    push :: Map.Map (Formula a) (W4.SymExpr sym SType)
         -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
         -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
         -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
         -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
         -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
         -> PrecFunType sym
         -> PrecFunType sym
         -> PrecFunType sym
         -> SymNode sym
         -> IO (W4.Pred sym)
    push formulaSymMap gamma smb struct stack ctx yield equal take xExpr = do
      let ioxp1 = W4.intLit sym 1 >>= W4.intAdd sym xExpr
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
      smbRule <- W4.intEq sym smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackRule <- W4.intEq sym stackxp1 xExpr
      -- stack(x) = 0 → ctx(x + 1) = 0
      sym0 <- W4.intLit sym 0
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      stackxEq0 <- W4.intEq sym stackx sym0
      ctxxp1Eq0 <- W4.intEq sym ctxxp1 sym0
      rootCtxRule <- W4.impliesPred sym stackxEq0 ctxxp1Eq0
      -- (stack(x) != 0 ∧ (push(x − 1) ∨ shift(x − 1))) → ctx(x + 1) = x − 1
      stackxNeq0 <- W4.intEq sym stackx sym0 >>= W4.notPred sym
      sym1 <- W4.intLit sym 1
      xm1 <- W4.intSub sym xExpr sym1
      pushxm1 <- checkPrec smb struct yield xm1
      shiftxm1 <- checkPrec smb struct equal xm1
      pushOrShiftxm1 <- W4.orPred sym pushxm1 shiftxm1
      stackxNeq0AndpushOrShiftxm1 <- W4.andPred sym stackxNeq0 pushOrShiftxm1
      ctxxp1Eqxm1 <- W4.intEq sym ctxxp1 xm1
      pushShiftCtxRule <- W4.impliesPred sym stackxNeq0AndpushOrShiftxm1 ctxxp1Eqxm1
      -- (stack(x) != 0 ∧ pop(x − 1)) → ctx(x + 1) = ctx(x)
      popxm1 <- checkPrec smb struct take xm1
      stackxNeq0AndPopxm1 <- W4.andPred sym stackxNeq0 popxm1
      ctxx <- W4.applySymFn sym ctx (Empty :> xExpr)
      ctxxp1Eqctxx <- W4.intEq sym ctxxp1 ctxx
      popCtxRule <- W4.impliesPred sym stackxNeq0AndPopxm1 ctxxp1Eqctxx
      -- Final and
      bigAndPred sym [ pnextRule, wpnextRule
                     , smbRule, stackRule
                     , rootCtxRule, pushShiftCtxRule, popCtxRule
                     ]

    -- SHIFT(xExpr)
    shift :: Map.Map (Formula a) (W4.SymExpr sym SType)
          -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
          -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
          -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
          -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
          -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
          -> SymNode sym
          -> IO (W4.Pred sym)
    shift formulaSymMap gamma smb struct stack ctx xExpr = do
      let ioxp1 = W4.intLit sym 1 >>= W4.intAdd sym xExpr
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
      smbRule <- W4.intEq sym smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      stackRule <- W4.intEq sym stackxp1 stackx
      -- ctx(x + 1) = ctx(x)
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      ctxx <- W4.applySymFn sym ctx (Empty :> xExpr)
      ctxRule <- W4.intEq sym ctxxp1 ctxx
      -- Final and
      bigAndPred sym [pnextRule, wpnextRule, smbRule, stackRule, ctxRule]

    -- POP(xExpr)
    pop :: W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
        -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
        -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
        -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
        -> SymNode sym
        -> IO (W4.Pred sym)
    pop gamma smb stack ctx xExpr = do
      xp1 <- W4.intLit sym 1 >>= W4.intAdd sym xExpr
      -- ∀p(Γ(p, x) ↔ Γ(p, x + 1))
      pSym <- W4.freshBoundVar sym (W4.safeSymbol "p") sRepr
      let pExpr = W4.varExpr sym pSym
      gammapx <- W4.applySymFn sym gamma (Empty :> pExpr :> xExpr)
      gammapxp1 <- W4.applySymFn sym gamma (Empty :> pExpr :> xp1)
      gammaIff <- W4.eqPred sym gammapx gammapxp1
      gammaRule <- W4.forallPred sym pSym gammaIff
      -- smb(x + 1) = smb(stack(x))
      smbxp1 <- W4.applySymFn sym smb (Empty :> xp1)
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      smbstackx <- W4.applySymFn sym smb (Empty :> stackx)
      smbRule <- W4.intEq sym smbxp1 smbstackx
      -- stack(x + 1) = stack(stack(x))
      stackxp1 <- W4.applySymFn sym stack (Empty :> xp1)
      stackstackx <- W4.applySymFn sym stack (Empty :> stackx)
      stackRule <- W4.intEq sym stackxp1 stackstackx
      -- ctx(x + 1) = ctx(stack(x))
      ctxxp1 <- W4.applySymFn sym ctx (Empty :> xp1)
      ctxstackx <- W4.applySymFn sym ctx (Empty :> stackx)
      ctxRule <- W4.intEq sym ctxxp1 ctxstackx
      -- Final and
      bigAndPred sym [gammaRule, smbRule, stackRule, ctxRule]

    -- END(xExpr)
    endTerm :: Map.Map (Formula a) (W4.SymExpr sym SType)
            -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
            -> SymNode sym
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
    conflict :: W4.SymFn sym (EmptyCtx ::> SType) W4.BaseBoolType
             -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
             -> SymNode sym
             -> IO (W4.Pred sym)
    conflict sigma gamma xExpr = do
      pSym <- W4.freshBoundVar sym (W4.safeSymbol "p") sRepr
      qSym <- W4.freshBoundVar sym (W4.safeSymbol "q") sRepr
      let pExpr = W4.varExpr sym pSym
          qExpr = W4.varExpr sym qSym
      sigmap <- W4.applySymFn sym sigma (Empty :> pExpr)
      sigmaq <- W4.applySymFn sym sigma (Empty :> qExpr)
      gammapx <- W4.applySymFn sym gamma (Empty :> pExpr :> xExpr)
      gammaqx <- W4.applySymFn sym gamma (Empty :> qExpr :> xExpr)
      andAll <- bigAndPred sym [sigmap, sigmaq, gammapx, gammaqx]
      pEqq <- W4.intEq sym pExpr qExpr
      pqImpl <- W4.impliesPred sym andAll pEqq
      forallq <- W4.forallPred sym qSym pqImpl
      W4.forallPred sym pSym forallq

    -- PNEXT(xExpr)
    pnext :: Map.Map (Formula a) (W4.SymExpr sym SType)
          -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
          -> W4.SymFn sym (EmptyCtx ::> NodeType) SType
          -> PrecFunType sym
          -> PrecFunType sym
          -> SymNode sym
          -> IO (W4.Pred sym)
    pnext fsm gamma struct yield take xExpr = do
      let pnextPrec prec g = do
            -- Γ(g, x)
            gammagx <- W4.applySymFn sym gamma (Empty :> (fsm Map.! g) :> xExpr)
            -- struct(x) prec struct(x + 1)
            structx <- W4.applySymFn sym struct (Empty :> xExpr)
            xp1 <- W4.intLit sym 1 >>= W4.intAdd sym xExpr
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
    emptyTerm :: Map.Map (Formula a) (W4.SymExpr sym SType)
              -> W4.SymFn sym (EmptyCtx ::> SType ::> NodeType) W4.BaseBoolType
              -> W4.SymFn sym (EmptyCtx ::> NodeType) NodeType
              -> SymNode sym
              -> IO (W4.Pred sym)
    emptyTerm fsm gamma stack xExpr = do
      -- Γ(#, x)
      gammaEndx <- W4.applySymFn sym gamma (Empty :> (fsm Map.! Atomic End) :> xExpr)
      -- stack(x) = 0
      stackx <- W4.applySymFn sym stack (Empty :> xExpr)
      sym0 <- W4.intLit sym 0
      stackxEq0 <- W4.intEq sym stackx sym0
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
