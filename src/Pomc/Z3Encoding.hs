{-# LANGUAGE ScopedTypeVariables #-}
{- |
   Module      : Pomc.Z3Encoding
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Z3Encoding ( SMTStatus(..)
                       , SMTResult(..)
                       , TableauNode(..)
                       , isSatisfiable
                       ) where

import Prelude hiding (take)

import Pomc.Prop (Prop(..))
import Pomc.Potl ( Dir(..), Formula(..), transformFold, pnf, atomic
                 , ltlNext, ltlBack, ltlPastAlways
                 )
import Pomc.Prec (Prec(..), Alphabet, isComplete)
import Pomc.Util (timeAction)

import Z3.Monad hiding (Result(..))
import qualified Z3.Monad as Z3

import qualified Control.Exception as E
import Control.Monad ((<=<), filterM)
import Data.List ((\\), intercalate)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.Word (Word64)

import qualified Debug.Trace as DBG

data SMTStatus = Sat | Unsat | Unknown deriving (Eq, Show)

data TableauNode = TableauNode { nodeGammaC :: [Formula String]
                               , nodeSmb    :: Prop String
                               , nodeStack  :: Integer
                               , nodeCtx    :: Integer
                               , nodeIdx    :: Integer
                               } deriving Eq

data SMTResult = SMTResult { smtStatus :: SMTStatus
                           , smtTableau :: Maybe [TableauNode]
                           , smtTimeAssert :: Double
                           , smtTimeCheck :: Double
                           , smtTimeModel :: Double
                           } deriving (Eq, Show)

instance Show TableauNode where
  show tn = "(" ++ (intercalate ", " [ show $ nodeIdx tn
                                     , show $ nodeGammaC tn
                                     , "smb = " ++ show (nodeSmb tn)
                                     , "stack = " ++ show (nodeStack tn)
                                     , "ctx = " ++ show (nodeCtx tn)
                                     ]) ++ ")"


isSatisfiable :: Alphabet String
              -> Formula String
              -> Word64
              -> IO SMTResult
isSatisfiable alphabet phi maxDepth = evalZ3 $ incrementalCheck 0 0 1
  where
    pnfPhi = pnf $ translate phi
    incrementalCheck assertTime checkTime k
      | k > maxDepth = return SMTResult { smtStatus = Unknown
                                        , smtTableau = Nothing
                                        , smtTimeAssert = assertTime
                                        , smtTimeCheck = checkTime
                                        , smtTimeModel = 0
                                        }
      | otherwise = do
          reset
          (tableauQuery, newAssertTime) <- timeAction $ assertEncoding alphabet pnfPhi k
          ((res, maybeModel), newCheckTime) <- timeAction $ solverCheckAndGetModel
          if res == Z3.Sat
            then do
            (tableau, modelTime) <- timeAction $ tableauQuery Nothing $ fromJust maybeModel
            return SMTResult { smtStatus = Sat
                             , smtTableau = Just tableau
                             , smtTimeAssert = assertTime + newAssertTime
                             , smtTimeCheck = checkTime + newCheckTime
                             , smtTimeModel = modelTime
                             }
            else incrementalCheck (assertTime + newAssertTime) (checkTime + newCheckTime) (k + 1)


assertEncoding :: Alphabet String
               -> Formula String
               -> Word64
               -> Z3 (Maybe Word64 -> Model -> Z3 [TableauNode])
assertEncoding alphabet phi k = do
  -- Sorts
  boolSort <- mkBoolSort
  nodeSortSymbol <- mkStringSymbol "NodeSort"
  nodeSort <- mkFiniteDomainSort nodeSortSymbol nodeSortSize
  (sSort, fConstMap) <- mkSSort
  -- Uninterpreted functions
  gamma  <- mkFreshFuncDecl "gamma" [sSort, nodeSort] boolSort
  sigma  <- mkFreshFuncDecl "sigma" [sSort] boolSort
  struct <- mkFreshFuncDecl "struct" [nodeSort] sSort
  smb    <- mkFreshFuncDecl "smb" [nodeSort] sSort
  yield  <- mkFreshFuncDecl "yield" [sSort, sSort] boolSort
  equal  <- mkFreshFuncDecl "equal" [sSort, sSort] boolSort
  take   <- mkFreshFuncDecl "take" [sSort, sSort] boolSort
  stack  <- mkFreshFuncDecl "stack" [nodeSort] nodeSort
  ctx    <- mkFreshFuncDecl "ctx" [nodeSort] nodeSort
  -- Encoding
  assert =<< mkPhiAxioms nodeSort fConstMap sigma struct smb gamma
  assert =<< mkPhiOPM fConstMap yield equal take

  -- xnf(φ)(1)
  node1 <- mkUnsignedInt64 1 nodeSort
  assert =<< groundxnf fConstMap gamma (xnf phi) node1

  -- smb(1) = #
  assert =<< mkEq (fConstMap Map.! Atomic End) =<< mkApp1 smb node1

  -- stack(1) = ⊥
  nodeBot <- mkUnsignedInt64 0 nodeSort
  assert =<< mkEq nodeBot =<< mkApp1 stack node1

  -- ctx(1) = ⊥
  assert =<< mkEq nodeBot =<< mkApp1 ctx node1

  -- start ∀x (...)
  -- x <= k
  assert =<< mkAndWith (\x -> do
                           xLit <- mkUnsignedInt64 x nodeSort
                           endx <- mkEndTerm fConstMap gamma xLit
                           conflictx <- mkConflict sSort sigma gamma xLit
                           mkAnd [endx, conflictx]
                       ) [1..k]

  -- x < k
  let mkTransitions x = do
        pnextx <- mkPnext nodeSort fConstMap gamma struct yield take x
        xLit <- mkUnsignedInt64 x nodeSort
        -- push(x) → PUSH(x)
        checkPushx <- mkCheckPrec smb struct yield xLit
        pushx <- mkPush nodeSort fConstMap gamma smb struct stack ctx yield equal take x
        pushxImpliesPushx <- mkImplies checkPushx pushx
        -- shift(x) → SHIFT(x)
        checkShiftx <- mkCheckPrec smb struct equal xLit
        shiftx <- mkShift nodeSort fConstMap gamma smb struct stack ctx x
        shiftxImpliesShiftx <- mkImplies checkShiftx shiftx
        -- pop(x) → POP(x)
        checkPopx <- mkCheckPrec smb struct take xLit
        popx <- mkPop sSort nodeSort gamma smb stack ctx x
        popxImpliesPopx <- mkImplies checkPopx popx
        mkAnd [pnextx, pushxImpliesPushx, shiftxImpliesShiftx, popxImpliesPopx]
  assert =<< mkAndWith mkTransitions [1..(k - 1)]
  -- end ∀x (...)

  -- EMPTY(k+1)
  assert =<< mkEmpty nodeSort fConstMap gamma stack k
  return $ queryTableau nodeSort fConstMap gamma smb stack ctx k
  where
    nodeSortSize = k + 1
    (structClos, clos) = closure alphabet phi

    mkSSort :: Z3 (Sort, Map (Formula String) AST)
    mkSSort = do
      constructors <- mapM (\f -> do
                               let fstring = show f
                               constrName <- mkStringSymbol fstring
                               recFnName <- mkStringSymbol $ "is_" ++ fstring
                               mkConstructor constrName recFnName [])
                      clos
      sSymbol <- mkStringSymbol "S"
      sSort <- mkDatatype sSymbol constructors
      constrFns <- getDatatypeSortConstructors sSort
      consts <- mapM (flip mkApp []) constrFns
      return (sSort, Map.fromList $ zip clos consts)

    mkPhiAxioms :: Sort -> Map (Formula String) AST
                -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Z3 AST
    mkPhiAxioms nodeSort fConstMap sigma struct smb gamma = do
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- mkAndWith (mkApp1 sigma . (fConstMap Map.!)) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- mkAndWith (mkNot <=< mkApp1 sigma . (fConstMap Map.!))
                            (clos \\ structClos)
      -- ∀x(Σ(struct(x)) ∧ Σ(smb(x)) ∧ Γ(struct(x), x))
      forall <- mkAndWith (\x -> do
                              xLit <- mkUnsignedInt64 x nodeSort
                              structX <- mkApp1 struct xLit
                              sigmaStructX <- mkApp1 sigma structX
                              sigmaSmbX    <- mkApp1 sigma =<< mkApp1 smb xLit
                              gammaStructXX <- mkApp gamma [structX, xLit]
                              mkAnd [sigmaStructX, sigmaSmbX, gammaStructXX]
                          ) [1..k]
      mkAnd [allStructInSigma, allOtherNotInSigma, forall]

    mkPhiOPM :: Map (Formula String) AST -> FuncDecl -> FuncDecl -> FuncDecl -> Z3 AST
    mkPhiOPM fConstMap yield equal take = E.assert (isComplete alphabet)
      $ mkAndWith assertPrecPair
      $ snd alphabet ++ (End, End, Equal):[(End, p, Yield) | p <- fst alphabet]
      where assertPrecPair (p, q, prec) = do
              let pqArg = [fConstMap Map.! Atomic p, fConstMap Map.! Atomic q]
                  (nPrec1, nPrec2) = getNegPrec prec
              posPrec  <- mkApp (getPosPrec prec) pqArg
              negPrec1 <- mkNot =<< mkApp nPrec1 pqArg
              negPrec2 <- mkNot =<< mkApp nPrec2 pqArg
              mkAnd [posPrec, negPrec1, negPrec2]

            getPosPrec Yield = yield
            getPosPrec Equal = equal
            getPosPrec Take = take

            getNegPrec Yield = (equal, take)
            getNegPrec Equal = (yield, take)
            getNegPrec Take = (yield, equal)

    -- xnf(f)_G(x)
    groundxnf :: Map (Formula String) AST -> FuncDecl -> Formula String -> AST -> Z3 AST
    groundxnf fConstMap gamma f x = case f of
      T                -> mkTrue
      Atomic _         -> applyGamma f
      Not T            -> mkFalse
      Not g@(Atomic _) -> mkNot =<< applyGamma g
      Not _            -> error "Supplied formula is not in Positive Normal Form."
      Or g h           -> boolPred (\a b -> mkOr [a, b]) g h
      And g h          -> boolPred (\a b -> mkAnd [a, b]) g h
      Xor g h          -> boolPred mkXor g h
      Implies g h      -> boolPred mkImplies g h
      Iff g h          -> boolPred mkEq g h
      PNext _ _        -> applyGamma f
      PBack _ _        -> error "Past operators not supported yet."
      WPNext _ _       -> applyGamma f
      XNext _ _        -> mkFalse -- applyGamma f
      XBack _ _        -> error "Past operators not supported yet."
      WXNext _ _       -> mkFalse -- applyGamma f
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
              glhs <- groundxnf fConstMap gamma lhs x
              grhs <- groundxnf fConstMap gamma rhs x
              op glhs grhs

            applyGamma g = mkApp gamma [fConstMap Map.! g, x]

    -- END(xExpr)
    mkEndTerm :: Map (Formula String) AST -> FuncDecl -> AST -> Z3 AST
    mkEndTerm fConstMap gamma x = do
      let noGamma g = mkNot =<< mkApp gamma [fConstMap Map.! g, x]
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap Map.! Atomic End, x]
      -- ∧_(PNext t α ∈ Cl(φ)) ¬Γ((PNext t α)_G, x)
      noGammaPNext <- mkAndWith noGamma [g | g@(PNext _ _) <- clos]
      -- ∧_(p ∈ AP) ¬Γ(p, x)
      noGammaAP <- mkAndWith noGamma [g | g@(Atomic (Prop _)) <- clos]
      noGammaPNextAndnoGammaAP <- mkAnd [noGammaPNext, noGammaAP]
      -- Final →
      mkImplies gammaEndx noGammaPNextAndnoGammaAP

    -- CONFLICT(x)
    mkConflict :: Sort -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkConflict sSort sigma gamma x = do
      pVar <- mkFreshConst "p" sSort
      pApp <- toApp pVar
      qVar <- mkFreshConst "q" sSort
      qApp <- toApp qVar
      sigmap <- mkApp1 sigma pVar
      sigmaq <- mkApp1 sigma qVar
      gammapx <- mkApp gamma [pVar, x]
      gammaqx <- mkApp gamma [qVar, x]
      andAll <- mkAnd [sigmap, sigmaq, gammapx, gammaqx]
      pEqq <- mkEq pVar qVar
      pqImpl <- mkImplies andAll pEqq
      mkForallConst [] [pApp, qApp] pqImpl

    -- PNEXT(xExpr)
    mkPnext :: Sort -> Map (Formula String) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Word64
            -> Z3 AST
    mkPnext nodeSort fConstMap gamma struct yield take x = do
      let pnextPrec prec g = do
            xLit <- mkUnsignedInt64 x nodeSort
            -- Γ(g, x)
            gammagx <- mkApp gamma [fConstMap Map.! g, xLit]
            -- struct(x) prec struct(x + 1)
            structx <- mkApp1 struct xLit
            xp1 <- mkUnsignedInt64 (x + 1) nodeSort
            structxp1 <- mkApp1 struct xp1
            structPrec <- mkApp prec [structx, structxp1]
            -- Final negated and
            mkNot =<< mkAnd [gammagx, structPrec]
      -- ∧_(PNext d α ∈ Cl(φ)) (...)
      pnextDown <- mkAndWith (pnextPrec take) [g | g@(PNext Down _) <- clos]
      -- ∧_(PNext u α ∈ Cl(φ)) (...)
      pnextUp <- mkAndWith (pnextPrec yield) [g | g@(PNext Up _) <- clos]
      mkAnd [pnextDown, pnextUp]

    -- push(xExpr), shift(xExpr), pop(xExpr)
    mkCheckPrec :: FuncDecl -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkCheckPrec smb struct precRel x = do
      smbX <- mkApp1 smb x
      structX <- mkApp1 struct x
      mkApp precRel [smbX, structX]

    -- PUSH(x)
    mkPush :: Sort -> Map (Formula String) AST
           -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
           -> FuncDecl -> FuncDecl -> FuncDecl -> Word64 -> Z3 AST
    mkPush nodeSort fConstMap gamma smb struct stack ctx yield equal take x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let propagateNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap Map.! next, xLit]
            rhs <- groundxnf fConstMap gamma (xnf arg) xp1
            mkEq lhs rhs
      -- big ands
      pnextRule <- mkAndWith propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- mkAndWith propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      smbxp1 <- mkApp1 smb xp1
      structx <- mkApp1 struct xLit
      smbRule <- mkEq smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- mkApp1 stack xp1
      stackRule <- mkEq stackxp1 xLit
      -- stack(x) = ⊥ → ctx(x + 1) = ⊥
      nodeBot <- mkUnsignedInt64 0 nodeSort
      stackx <- mkApp1 stack xLit
      ctxxp1 <- mkApp1 ctx xp1
      stackxEqBot <- mkEq stackx nodeBot
      ctxxp1EqBot <- mkEq ctxxp1 nodeBot
      botCtxRule <- mkImplies stackxEqBot ctxxp1EqBot
      -- (stack(x) != ⊥ ∧ (push(x − 1) ∨ shift(x − 1))) → ctx(x + 1) = x − 1
      stackxNeqBot <- mkNot =<< mkEq stackx nodeBot
      xm1 <- mkUnsignedInt64 (x - 1) nodeSort
      pushxm1 <- mkCheckPrec smb struct yield xm1
      shiftxm1 <- mkCheckPrec smb struct equal xm1
      pushOrShiftxm1 <- mkOr [pushxm1, shiftxm1]
      stackxNeqBotAndpushOrShiftxm1 <- mkAnd [stackxNeqBot, pushOrShiftxm1]
      ctxxp1Eqxm1 <- mkEq ctxxp1 xm1
      pushShiftCtxRule <- mkImplies stackxNeqBotAndpushOrShiftxm1 ctxxp1Eqxm1
      -- (stack(x) != ⊥ ∧ pop(x − 1)) → ctx(x + 1) = ctx(x)
      popxm1 <- mkCheckPrec smb struct take xm1
      stackxNeqBotAndPopxm1 <- mkAnd [stackxNeqBot, popxm1]
      ctxx <- mkApp1 ctx xLit
      ctxxp1Eqctxx <- mkEq ctxxp1 ctxx
      popCtxRule <- mkImplies stackxNeqBotAndPopxm1 ctxxp1Eqctxx
      -- Final and
      mkAnd [ pnextRule, wpnextRule
            , smbRule, stackRule
            , botCtxRule, pushShiftCtxRule, popCtxRule
            ]

    -- SHIFT(x)
    mkShift :: Sort -> Map (Formula String) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
            -> Word64 -> Z3 AST
    mkShift nodeSort fConstMap gamma smb struct stack ctx x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let propagateNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap Map.! next, xLit]
            rhs <- groundxnf fConstMap gamma (xnf arg) xp1
            mkImplies lhs rhs
      -- big ands
      pnextRule <- mkAndWith propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- mkAndWith propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      smbxp1 <- mkApp1 smb xp1
      structx <- mkApp1 struct xLit
      smbRule <- mkEq smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- mkApp1 stack xp1
      stackx <- mkApp1 stack xLit
      stackRule <- mkEq stackxp1 stackx
      -- ctx(x + 1) = ctx(x)
      ctxxp1 <- mkApp1 ctx xp1
      ctxx <- mkApp1 ctx xLit
      ctxRule <- mkEq ctxxp1 ctxx
      -- Final and
      mkAnd [pnextRule, wpnextRule, smbRule, stackRule, ctxRule]

    -- POP(xExpr)
    mkPop :: Sort -> Sort -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Word64
          -> Z3 AST
    mkPop sSort nodeSort gamma smb stack ctx x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      -- ∀p(Γ(p, x) ↔ Γ(p, x + 1))
      pVar <- mkFreshConst "p" sSort
      pApp <- toApp pVar
      gammapx <- mkApp gamma [pVar, xLit]
      gammapxp1 <- mkApp gamma [pVar, xp1]
      gammaIff <- mkIff gammapx gammapxp1
      gammaRule <- mkForallConst [] [pApp] gammaIff
      -- smb(x + 1) = smb(stack(x))
      smbxp1 <- mkApp1 smb xp1
      stackx <- mkApp1 stack xLit
      smbstackx <- mkApp1 smb stackx
      smbRule <- mkEq smbxp1 smbstackx
      -- stack(x + 1) = stack(stack(x))
      stackxp1 <- mkApp1 stack xp1
      stackstackx <- mkApp1 stack stackx
      stackRule <- mkEq stackxp1 stackstackx
      -- ctx(x + 1) = ctx(stack(x))
      ctxxp1 <- mkApp1 ctx xp1
      ctxstackx <- mkApp1 ctx stackx
      ctxRule <- mkEq ctxxp1 ctxstackx
      -- Final and
      mkAnd [gammaRule, smbRule, stackRule, ctxRule]

    -- EMPTY(x)
    mkEmpty :: Sort -> Map (Formula String) AST -> FuncDecl -> FuncDecl -> Word64 -> Z3 AST
    mkEmpty nodeSort fConstMap gamma stack x = do
      xLit <- mkUnsignedInt64 x nodeSort
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap Map.! Atomic End, xLit]
      -- stack(x) = ⊥
      stackx <- mkApp1 stack xLit
      stackxEqBot <- mkEq stackx =<< mkUnsignedInt64 0 nodeSort
      mkAnd [gammaEndx, stackxEqBot]


mkApp1 :: FuncDecl -> AST -> Z3 AST
mkApp1 f x = mkApp f [x]


mkAndWith :: (a -> Z3 AST) -> [a] -> Z3 AST
mkAndWith predGen items = mapM predGen items >>= mkAnd


closure :: Alphabet String -> Formula String -> ([Formula String], [Formula String])
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

xnf :: Formula String -> Formula String
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
  Eventually g    -> error "LTL operators only supported through translation."
  Always g        -> error "LTL operators only supported through translation."
  AuxBack _ _     -> error "AuxBack not supported in SMT encoding."

translate :: Formula String -> Formula String
translate phi = fst $ transformFold applyTransl 0 phi where
  applyTransl f upId = case f of
    HNext dir g    -> let qEta = mkUniqueProp upId
      in ( gammaLR dir qEta
           `And` ltlNext (Until Up (Not $ xOp dir qEta) ((Not $ xOp dir qEta) `And` g))
         , upId + 1
         )
    HBack dir g    -> let qEta = mkUniqueProp upId
      in ( gammaLR dir qEta
           `And` ltlBack (Since Up (Not $ xOp dir qEta) ((Not $ xOp dir qEta) `And` g))
         , upId + 1
         )
    HUntil dir g h -> let qEta = mkUniqueProp upId
      in ( gammaLR dir qEta
           `And` (Until Up (xOp dir qEta `Implies` g) (xOp dir qEta `And` h))
         , upId + 1
         )
    HSince dir g h -> let qEta = mkUniqueProp upId
      in ( gammaLR dir qEta
           `And` (Since Up (xOp dir qEta `Implies` g) (xOp dir qEta `And` h))
         , upId + 1
         )
    Eventually g   -> (Until Up T . Until Down T $ g, upId)
    Always g       -> (Not . Until Up T . Until Down T . Not $ g, upId)
    _              -> (f, upId)

  -- xOp is correct only because qEta holds in a single position, not in general.
  mkUniqueProp n = Atomic . Prop $ "@" ++ show n
  xOp Up psi = XBack Down psi `And` Not (XBack Up psi)
  xOp Down psi = XNext Up psi `And` Not (XNext Down psi)
  gammaLR dir qEta = xOp dir $ qEta
    `And` (ltlNext . Always . Not $ qEta)
    `And` (ltlBack . ltlPastAlways . Not $ qEta)


queryTableau :: Sort -> Map (Formula String) AST
             -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
             -> Word64 -> Maybe Word64 -> Model -> Z3 [TableauNode]
queryTableau nodeSort fConstMap gamma smb stack ctx k maxLen model = do
  let unrollLength = case maxLen of
        Just ml -> min k ml
        Nothing -> k
  mapM queryTableauNode [1..unrollLength]
  where
    fConstList = Map.toList fConstMap
    constPropMap = Map.fromList $ map (\(Atomic p, fConst) -> (fConst, p))
                   $ filter (atomic . fst) fConstList
    queryTableauNode idx = do
      idxNode <- mkUnsignedInt64 idx nodeSort
      gammaVals <- filterM (\(_, fConst) -> fromJust <$>
                             (evalBool model =<< mkApp gamma [fConst, idxNode])) fConstList
      Just smbVal <- eval model =<< mkApp1 smb idxNode
      Just stackVal <- evalInt model =<< mkApp1 stack idxNode
      Just ctxVal <- evalInt model =<< mkApp1 ctx idxNode
      return TableauNode { nodeGammaC = map fst gammaVals
                         , nodeSmb = constPropMap Map.! smbVal
                         , nodeStack = stackVal
                         , nodeCtx = ctxVal
                         , nodeIdx = fromIntegral idx
                         }
