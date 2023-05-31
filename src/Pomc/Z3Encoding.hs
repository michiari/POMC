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
                       , modelCheckProgram
                       ) where

import Prelude hiding (take)

import Pomc.Prop (Prop(..))
import Pomc.Potl ( Dir(..), Formula(..), transformFold, pnf, atomic
                 , ltlNext, ltlBack, ltlPastAlways
                 )
import Pomc.Prec (Prec(..), Alphabet, isComplete)
import Pomc.Util (timeAction)
import qualified Pomc.MiniProc as MP

import Z3.Monad hiding (Result(..))
import qualified Z3.Monad as Z3

import qualified Control.Exception as E
import Control.Monad ((<=<), filterM)
import Data.List ((\\), intercalate, find)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)
import Data.Word (Word64)
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.BitVector as BV
import qualified Data.Text as T

import qualified Debug.Trace as DBG

data SMTStatus = Sat | Unsat | Unknown deriving (Eq, Show)

data TableauNode = TableauNode { nodeGammaC :: [Formula MP.ExprProp]
                               , nodeSmb    :: Prop MP.ExprProp
                               , nodeStack  :: Integer
                               , nodeCtx    :: Integer
                               , nodeIdx    :: Integer
                               } deriving Eq

data SMTResult = SMTResult { smtStatus        :: SMTStatus
                           , smtTableau       :: Maybe [TableauNode]
                           , smtTimeAssert    :: Double
                           , smtTimeCheck     :: Double
                           , smtTimeModel     :: Double
                           , smtTimeLastCheck :: Double
                           } deriving (Eq, Show)

instance Show TableauNode where
  show tn = "(" ++ (intercalate ", " [ show $ nodeIdx tn
                                     , show $ nodeGammaC tn
                                     , "smb = " ++ show (nodeSmb tn)
                                     , "stack = " ++ show (nodeStack tn)
                                     , "ctx = " ++ show (nodeCtx tn)
                                     ]) ++ ")"

data Query = SatQuery { qAlphabet :: Alphabet MP.ExprProp }
             | MiniProcQuery { qProg :: MP.Program }
             deriving Show

isSatisfiable :: Alphabet String
              -> Formula String
              -> Word64
              -> IO SMTResult
isSatisfiable alphabet phi maxDepth =
  checkQuery epPhi (SatQuery epAlphabet) maxDepth
  where
    epPhi = fmap (MP.TextProp . T.pack) phi
    epAlphabet = MP.stringToExprPropAlphabet alphabet

modelCheckProgram :: Formula MP.ExprProp -> MP.Program -> Word64 -> IO SMTResult
modelCheckProgram phi prog maxDepth = do
  res <- checkQuery (Not phi) (MiniProcQuery prog) maxDepth
  return res { smtStatus = flipStatus $ smtStatus res }
  where flipStatus Sat = Unsat
        flipStatus Unsat = Sat
        flipStatus Unknown = Unknown

checkQuery :: Formula MP.ExprProp
           -> Query
           -> Word64
           -> IO SMTResult
checkQuery phi query maxDepth = evalZ3 $ incrementalCheck 0 0 0 minLength
  where
    pnfPhi = pnf $ translate phi
    minLength = case query of
      SatQuery {} -> 1
      MiniProcQuery {} -> 2
    incrementalCheck assertTime checkTime lastCheckTime k
      | k > maxDepth = return SMTResult { smtStatus = Unknown
                                        , smtTableau = Nothing
                                        , smtTimeAssert = assertTime
                                        , smtTimeCheck = checkTime
                                        , smtTimeModel = 0
                                        , smtTimeLastCheck = lastCheckTime
                                        }
      | otherwise = do
          reset
          (tableauQuery, newAssertTime) <- timeAction $ assertEncoding pnfPhi query k
          ((res, maybeModel), newCheckTime) <- timeAction $ solverCheckAndGetModel
          if res == Z3.Sat
            then do
            (tableau, modelTime) <- timeAction $ tableauQuery Nothing $ fromJust maybeModel
            -- DBG.traceM =<< showModel (fromJust maybeModel)
            return SMTResult { smtStatus = Sat
                             , smtTableau = Just tableau
                             , smtTimeAssert = assertTime + newAssertTime
                             , smtTimeCheck = checkTime + newCheckTime
                             , smtTimeModel = modelTime
                             , smtTimeLastCheck = newCheckTime
                             }
            else incrementalCheck (assertTime + newAssertTime)
                 (checkTime + newCheckTime) newCheckTime (k + 1)


assertEncoding :: Formula MP.ExprProp
               -> Query
               -> Word64
               -> Z3 (Maybe Word64 -> Model -> Z3 [TableauNode])
assertEncoding phi query k = do
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
  assert =<< mkEq (fConstMap M.! Atomic End) =<< mkApp1 smb node1

  -- stack(1) = ⊥
  nodeBot <- mkUnsignedInt64 0 nodeSort -- Note: all quantifiers on nodes should exclude 0
  assert =<< mkEq nodeBot =<< mkApp1 stack node1

  -- ctx(1) = ⊥
  assert =<< mkEq nodeBot =<< mkApp1 ctx node1

  -- start ∀x (...)
  -- x <= k
  let mkTermRules x = do
        xLit <- mkUnsignedInt64 x nodeSort
        checkPushx <- mkCheckPrec smb struct yield xLit
        checkShiftx <- mkCheckPrec smb struct equal xLit
        checkPopx <- mkCheckPrec smb struct take xLit
        inputx <- mkOr [checkPushx, checkShiftx]
        -- xnextx
        xnextx <- mkXnext nodeSort fConstMap gamma smb struct ctx yield equal take x
        inputxImpliesXnextx <- mkImplies inputx xnextx
        -- wxnextx
        wxnextx <- mkWxnext nodeSort fConstMap gamma struct ctx yield equal take x
        popxImpliesWxnextx <- mkImplies checkPopx wxnextx
        endx <- mkEndTerm fConstMap gamma xLit
        conflictx <- mkConflict sSort sigma gamma xLit
        mkAnd [inputxImpliesXnextx, popxImpliesWxnextx, endx, conflictx]
  assert =<< mkForallNodes [1..k] mkTermRules

  -- x < k
  let mkTransitions x = do
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
        -- pnextx
        pnextx <- mkPnext nodeSort fConstMap gamma struct yield take x
        inputx <- mkOr [checkPushx, checkShiftx]
        inputxImpliesPnextx <- mkImplies inputx pnextx
        mkAnd [ pushxImpliesPushx, shiftxImpliesShiftx, popxImpliesPopx
              , inputxImpliesPnextx
              ]
  assert =<< mkForallNodes [1..(k - 1)] mkTransitions
  -- end ∀x (...)

  -- EMPTY(k)
  assert =<< mkEmpty nodeSort fConstMap gamma stack k

  case query of
    SatQuery _ -> return ()
    MiniProcQuery prog ->
      encodeProg nodeSort fConstMap gamma struct smb yield equal take stack prog k

  return $ queryTableau nodeSort fConstMap gamma smb stack ctx k
  where
    nodeSortSize = k + 1
    alphabet = case query of
      SatQuery a -> a
      MiniProcQuery _ -> MP.miniProcAlphabet
    (structClos, clos) = closure alphabet phi

    mkSSort :: Z3 (Sort, Map (Formula MP.ExprProp) AST)
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
      return (sSort, M.fromList $ zip clos consts)

    mkPhiAxioms :: Sort -> Map (Formula MP.ExprProp) AST
                -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Z3 AST
    mkPhiAxioms nodeSort fConstMap sigma struct smb gamma = do
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- mkAndWith (mkApp1 sigma . (fConstMap M.!)) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- mkAndWith (mkNot <=< mkApp1 sigma . (fConstMap M.!))
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

    mkPhiOPM :: Map (Formula MP.ExprProp) AST -> FuncDecl -> FuncDecl -> FuncDecl
             -> Z3 AST
    mkPhiOPM fConstMap yield equal take = E.assert (isComplete alphabet)
      $ mkAndWith assertPrecPair
      $ snd alphabet ++ (End, End, Equal):[(End, p, Yield) | p <- fst alphabet]
      where assertPrecPair (p, q, prec) = do
              let pqArg = [fConstMap M.! Atomic p, fConstMap M.! Atomic q]
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
    groundxnf :: Map (Formula MP.ExprProp) AST -> FuncDecl -> Formula MP.ExprProp
              -> AST -> Z3 AST
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
              glhs <- groundxnf fConstMap gamma lhs x
              grhs <- groundxnf fConstMap gamma rhs x
              op glhs grhs

            applyGamma g = mkApp gamma [fConstMap M.! g, x]

    -- END(xExpr)
    mkEndTerm :: Map (Formula MP.ExprProp) AST -> FuncDecl -> AST -> Z3 AST
    mkEndTerm fConstMap gamma x = do
      let noGamma g = mkNot =<< mkApp gamma [fConstMap M.! g, x]
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap M.! Atomic End, x]
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

    -- PNEXT(x) ∧ WPNEXT(x)
    mkPnext :: Sort -> Map (Formula MP.ExprProp) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Word64
            -> Z3 AST
    mkPnext nodeSort fConstMap gamma struct yield take x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let pnextPrec prec g = do
            -- Γ(g, x)
            gammagx <- mkApp gamma [fConstMap M.! g, xLit]
            -- struct(x) prec struct(x + 1)
            structx <- mkApp1 struct xLit
            structxp1 <- mkApp1 struct xp1
            structPrec <- mkApp prec [structx, structxp1]
            -- Final negated and
            mkNot =<< mkAnd [gammagx, structPrec]
      -- ∧_(PNext d α ∈ Cl(φ)) (...)
      pnextDown <- mkAndWith (pnextPrec take) [g | g@(PNext Down _) <- clos]
      -- ∧_(PNext u α ∈ Cl(φ)) (...)
      pnextUp <- mkAndWith (pnextPrec yield) [g | g@(PNext Up _) <- clos]
      let wpnextPrec prec (g, arg) = do
            -- Γ(g, x)
            gammagx <- mkApp gamma [fConstMap M.! g, xLit]
            -- Γ(h, x + 1)
            gammahxp1 <- groundxnf fConstMap gamma (xnf arg) xp1
            -- struct(x) prec struct(x + 1)
            structx <- mkApp1 struct xLit
            structxp1 <- mkApp1 struct xp1
            structPrec <- mkApp prec [structx, structxp1]
            -- Final implication
            notStructPrec <- mkNot structPrec
            gammagxAndNotStructPrec <- mkAnd [gammagx, notStructPrec]
            mkImplies gammagxAndNotStructPrec gammahxp1
      wpnextDown <- mkAndWith (wpnextPrec take) [(g, arg) | g@(WPNext Down arg) <- clos]
      wpnextUp <- mkAndWith (wpnextPrec yield) [(g, arg) | g@(WPNext Up arg) <- clos]
      mkAnd [pnextDown, pnextUp, wpnextDown, wpnextUp]

    -- XNEXT(x)
    mkXnext :: Sort -> Map (Formula MP.ExprProp) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
            -> FuncDecl -> FuncDecl -> FuncDecl -> Word64
            -> Z3 AST
    mkXnext nodeSort fConstMap gamma smb struct ctx yield equal take x = do
      xLit <- mkUnsignedInt64 x nodeSort
      structx <- mkApp1 struct xLit
      let xnextSat g@(XNext dir arg) = do
            gammagx <- mkApp gamma [fConstMap M.! g, xLit]
            let satisfied z = do
                  zLit <- mkUnsignedInt64 z nodeSort
                  checkPopz <- mkCheckPrec smb struct take zLit
                  ctxz <- mkApp1 ctx zLit
                  ctxzEqx <- mkEq ctxz xLit
                  xnfArgz <- groundxnf fConstMap gamma (xnf arg) zLit
                  structz <- mkApp1 struct zLit
                  precYT <- case dir of
                    Down -> mkApp yield [structx, structz]
                    Up   -> mkApp take [structx, structz]
                  precEq <- mkApp equal [structx, structz]
                  orPrec <- mkOr [precYT, precEq]
                  mkAnd [checkPopz, ctxzEqx, xnfArgz, orPrec]
            exists <- mkExistsNodes [x..k] satisfied
            -- Implies
            mkImplies gammagx exists
          xnextSat _ = error "XNext formula expected."
      mkAndWith xnextSat [g | g@(XNext _ _) <- clos]

    mkWxnext :: Sort -> Map (Formula MP.ExprProp) AST
             -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
             -> FuncDecl -> FuncDecl -> Word64
             -> Z3 AST
    mkWxnext nodeSort fConstMap gamma struct ctx yield equal take x = do
      xLit <- mkUnsignedInt64 x nodeSort
      structx <- mkApp1 struct xLit
      ctxx <- mkApp1 ctx xLit
      structCtxx <- mkApp1 struct ctxx
      let wxnextSat g@(WXNext dir arg) = do
            gammagctxx <- mkApp gamma [fConstMap M.! g, ctxx]
            precYT <- case dir of
              Down -> mkApp yield [structCtxx, structx]
              Up   -> mkApp take [structCtxx, structx]
            precEq <- mkApp equal [structCtxx, structx]
            orPrec <- mkOr [precYT, precEq]
            gammagctxxAndOrPrec <- mkAnd [gammagctxx, orPrec]
            xnfArgx <- groundxnf fConstMap gamma (xnf arg) xLit
            mkImplies gammagctxxAndOrPrec xnfArgx
      mkAndWith wxnextSat [g | g@(WXNext _ _) <- clos]

    -- PUSH(x)
    mkPush :: Sort -> Map (Formula MP.ExprProp) AST
           -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
           -> FuncDecl -> FuncDecl -> FuncDecl -> Word64 -> Z3 AST
    mkPush nodeSort fConstMap gamma smb struct stack ctx yield equal take x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let propagatePNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap M.! next, xLit]
            rhs <- groundxnf fConstMap gamma (xnf arg) xp1
            mkImplies lhs rhs
      -- big and
      pnextRule <- mkAndWith propagatePNext [(g, alpha) | g@(PNext _ alpha) <- clos]
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
      -- (stack(x) != ⊥ ∧ pop(x − 1)) → ctx(x + 1) = ctx(x - 1)
      popxm1 <- mkCheckPrec smb struct take xm1
      stackxNeqBotAndPopxm1 <- mkAnd [stackxNeqBot, popxm1]
      ctxxm1 <- mkApp1 ctx xm1
      ctxxp1Eqctxx <- mkEq ctxxp1 ctxxm1
      popCtxRule <- mkImplies stackxNeqBotAndPopxm1 ctxxp1Eqctxx
      -- Final and
      mkAnd [ pnextRule
            , smbRule, stackRule
            , botCtxRule, pushShiftCtxRule, popCtxRule
            ]

    -- SHIFT(x)
    mkShift :: Sort -> Map (Formula MP.ExprProp) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
            -> Word64 -> Z3 AST
    mkShift nodeSort fConstMap gamma smb struct stack ctx x = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let propagatePNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap M.! next, xLit]
            rhs <- groundxnf fConstMap gamma (xnf arg) xp1
            mkImplies lhs rhs
      -- big ands
      pnextRule <- mkAndWith propagatePNext [(g, alpha) | g@(PNext _ alpha) <- clos]
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
      mkAnd [pnextRule, smbRule, stackRule, ctxRule]

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
    mkEmpty :: Sort -> Map (Formula MP.ExprProp) AST -> FuncDecl -> FuncDecl
            -> Word64 -> Z3 AST
    mkEmpty nodeSort fConstMap gamma stack x = do
      xLit <- mkUnsignedInt64 x nodeSort
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap M.! Atomic End, xLit]
      -- stack(x) = ⊥
      stackx <- mkApp1 stack xLit
      stackxEqBot <- mkEq stackx =<< mkUnsignedInt64 0 nodeSort
      mkAnd [gammaEndx, stackxEqBot]


encodeProg :: Sort -> Map (Formula MP.ExprProp) AST
           -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
           -> FuncDecl -> FuncDecl -> FuncDecl
           -> MP.Program -> Word64 -> Z3 ()
encodeProg nodeSort fConstMap gamma struct smb yield equal take stack prog k = do
  let (lowerState, ini, fin) = MP.sksToExtendedOpa False (MP.pSks prog)
  locSortSymbol <- mkStringSymbol "LocSort"
  locSort <- mkFiniteDomainSort locSortSymbol $ fromIntegral $ MP.lsSid lowerState
  -- Uninterpreted functions
  pc <- mkFreshFuncDecl "pc" [nodeSort] locSort
  sVarFunVec <- mkVarFunctions
  -- Initial locations
  node1 <- mkUnsignedInt64 1 nodeSort
  assert =<< mkOrWith (\l -> do
                          lLit <- mkUnsignedInt l locSort
                          pc1 <- mkApp1 pc node1
                          mkEq pc1 lLit
                      ) ini
  -- Initialize variables
  nodeBot <- mkUnsignedInt64 0 nodeSort
  assert =<< mkInit0 sVarFunVec allScalars nodeBot
  assert =<< mkInit0 sVarFunVec allScalars node1
  -- start ∀x (...)
  -- x < k
  let mkProgTransitions x = do
        xLit <- mkUnsignedInt64 x nodeSort
        -- push(x) → PUSH(x)
        checkPushx <- mkCheckPrec smb struct yield xLit
        pushProgx <- mkInput sVarFunVec locSort pc (MP.lsDPush lowerState) x
        pushxImpliesPushProgx <- mkImplies checkPushx pushProgx
        -- shift(x) → SHIFT(x)
        checkShiftx <- mkCheckPrec smb struct equal xLit
        shiftProgx <- mkInput sVarFunVec locSort pc (MP.lsDShift lowerState) x
        shiftxImpliesShiftProgx <- mkImplies checkShiftx shiftProgx
        -- pop(x) → POP(x)
        checkPopx <- mkCheckPrec smb struct take xLit
        popProgx <- mkPop sVarFunVec locSort pc (MP.lsDPop lowerState) x
        popxImpliesPopProgx <- mkImplies checkPopx popProgx
        mkAnd [pushxImpliesPushProgx, shiftxImpliesShiftProgx, popxImpliesPopProgx]
  assert =<< mkAndWith mkProgTransitions [1..(k - 1)]
  -- end ∀x (...)
  -- Final states
  nodek <- mkUnsignedInt64 k nodeSort
  assert =<< mkOrWith (\l -> do
                          lLit <- mkUnsignedInt l locSort
                          pck <- mkApp1 pc nodek
                          mkEq pck lLit
                      ) fin
  where
    apConstMap = M.fromList
      $ foldr (\(p, c) rest -> case p of
                  Atomic tp@(Prop (MP.TextProp t))
                    | tp `notElem` (fst MP.miniProcAlphabet) -> (t, c):rest
                  _ -> rest
              ) []
      $ M.toList fConstMap
    exprPropMap = foldr (\(exprF, exprS) rest -> case exprF of
                            Atomic (Prop (MP.ExprProp s e)) -> (s, e, exprS):rest
                            _ -> rest
                        ) []
                  $ M.toList fConstMap
    allScalars = S.toList (MP.pGlobalScalars prog) ++ S.toList (MP.pLocalScalars prog)
    mkVarFunctions = -- TODO: fix ID clash in local variables
      let mkSVarFun varList vid = do
            let var = fromJust $ find (\v -> MP.varId v == vid) varList
            varSym <- mkIntSymbol $ MP.varId var
            varSort <- mkBvSort $ MP.varWidth var
            varFunc <- mkFuncDecl varSym [nodeSort] varSort
            return (varFunc, varSort)

      in V.generateM (length allScalars) (mkSVarFun allScalars)

    mkInit0 :: Vector (FuncDecl, Sort) -> [MP.Variable] -> AST -> Z3 AST
    mkInit0 sVarFunVec vars xLit =
      mkAndWith (\v -> do
                    let (vFunc, s) = sVarFunVec V.! MP.varId v
                    val0 <- mkUnsignedInt 0 s
                    vx <- mkApp1 vFunc xLit
                    mkEq vx val0
                ) vars

    mkInput :: Vector (FuncDecl, Sort) -> Sort -> FuncDecl
            -> Map Word (MP.InputLabel, MP.DeltaTarget) -> Word64 -> Z3 AST
    mkInput sVarFunVec locSort pc lsDelta x =
      mkOrWith mkTransition $ M.toList lsDelta where
      mkTransition (l1, (il, MP.States dt)) = do
        xLit <- mkUnsignedInt64 x nodeSort
        xp1 <- mkUnsignedInt64 (x + 1) nodeSort
        -- pc(x) = l1
        l1Lit <- mkUnsignedInt l1 locSort
        pcX <- mkApp1 pc xLit
        pcXEqL1 <- mkEq l1Lit pcX
        -- ∧_(p∈b) Γ(p, x)
        structX <- mkApp1 struct xLit
        structXEqil <- mkEq (fConstMap M.! (Atomic . Prop . MP.TextProp . MP.ilStruct $ il)) structX
        let inputNames = (MP.ilFunction il) : (MP.ilModules il)
        inputProps <- mkAndWith (\(l, c) -> let pn | l `elem` inputNames = return
                                                   | otherwise = mkNot
                                            in pn =<< mkApp gamma [c, xLit]
                                ) $ M.toList apConstMap
        -- assert ExprProps
        let assertExprProp (scope, expr, exprS) = do
              gammaExprx <- mkApp gamma [exprS, xLit]
              if isNothing scope || fromJust scope == MP.ilFunction il
                then mkIff gammaExprx =<< evalBoolExpr sVarFunVec expr xLit
                else mkNot gammaExprx
        exprProps <- mkAndWith assertExprProp exprPropMap
        -- ACTION(x, _, a)
        action <- mkAction sVarFunVec x Nothing $ MP.ilAction il
        -- g|x ∧ pc(x + 1) = l2
        targets <- mkOrWith (\(g, l2) -> do
                                -- pc(x + 1) = l2
                                l2Lit <- mkUnsignedInt l2 locSort
                                pcXp1 <- mkApp1 pc xp1
                                nextPc <- mkEq pcXp1 l2Lit
                                case g of
                                  MP.NoGuard -> return nextPc
                                  MP.Guard e -> do
                                    guard <- evalBoolExpr sVarFunVec e xLit
                                    mkAnd [guard, nextPc]
                            ) dt
        mkAnd [pcXEqL1, structXEqil, inputProps, action, exprProps, targets]

    mkPop :: Vector (FuncDecl, Sort) -> Sort -> FuncDecl
          -> Map (Word, Word) (MP.Action, MP.DeltaTarget) -> Word64 -> Z3 AST
    mkPop sVarFunVec locSort pc lsDelta x =
      mkOrWith mkTransition $ M.toList lsDelta where
      mkTransition ((l1, ls), (act, MP.States dt)) = do
        xLit <- mkUnsignedInt64 x nodeSort
        xp1 <- mkUnsignedInt64 (x + 1) nodeSort
        -- pc(x) = l1
        l1Lit <- mkUnsignedInt l1 locSort
        pcX <- mkApp1 pc xLit
        pcXEqL1 <- mkEq pcX l1Lit
        -- pc(stack(x)) = ls
        stackX <- mkApp1 stack xLit
        lsLit <- mkUnsignedInt ls locSort
        pcStackX <- mkApp1 pc stackX
        pcStackXEqLs <- mkEq pcStackX lsLit
        -- ACTION(x, stack(x), a)
        action <- mkAction sVarFunVec x (Just stackX) act
        -- g|x ∧ pc(x + 1) = l2
        targets <- mkOrWith (\(g, l2) -> do
                                -- pc(x + 1) = l2
                                l2Lit <- mkUnsignedInt l2 locSort
                                pcXp1 <- mkApp1 pc xp1
                                nextPc <- mkEq pcXp1 l2Lit
                                case g of
                                  MP.NoGuard -> return nextPc
                                  MP.Guard e -> do
                                    guard <- evalBoolExpr sVarFunVec e xLit
                                    mkAnd [guard, nextPc]
                            ) dt
        mkAnd [pcXEqL1, pcStackXEqLs, action, targets]

    mkAction :: Vector (FuncDecl, Sort) -> Word64 -> Maybe AST -> MP.Action -> Z3 AST
    mkAction sVarFunVec x poppedNode action = do
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      let propvals :: [MP.Variable] -> Z3 AST
          propvals except =
            let excSet = S.fromList $ map MP.varId except
            in mkAnd =<< V.ifoldM (\rest i (vf, _) -> if i `S.member` excSet
                                    then return rest
                                    else do
                                      vfx <- mkApp1 vf xLit
                                      vfxp1 <- mkApp1 vf xp1
                                      vfxEqVfxp1 <- mkEq vfx vfxp1
                                      return $ vfxEqVfxp1:rest
                                  ) [] sVarFunVec
      case action of
        MP.Noop -> propvals []
        MP.Assign (MP.LScalar lhs) rhs -> do
          -- Do assignment
          evalRhs <- evalExpr sVarFunVec rhs xLit
          lhsXp1 <- mkApp1 (fst $ sVarFunVec V.! MP.varId lhs) xp1
          lhsXp1EqRhs <- mkEq lhsXp1 evalRhs
          -- Propagate all remaining variables
          propagate <- propvals [lhs]
          mkAnd [lhsXp1EqRhs, propagate]
        MP.Assign (MP.LArray _var _idxExpr) _rhs -> error "Arrays not supported yet."
        MP.Nondet (MP.LScalar var) -> propvals [var]
        MP.Nondet (MP.LArray _var _idxExpr) -> error "Arrays not supported yet."
        MP.CallOp fname fargs aargs -> do
          -- Assign parameters
          let assign (farg, aarg) = do
                fxp1 <- mkApp1 (fst $ sVarFunVec V.! MP.varId (getFargVar farg)) xp1
                evalAarg <- case aarg of
                  MP.ActualVal e      -> evalExpr sVarFunVec e xLit
                  MP.ActualValRes var -> mkApp1 (fst $ sVarFunVec V.! MP.varId var) xLit
                mkEq fxp1 evalAarg
          params <- mkAndWith assign $ zip fargs aargs
          -- Initialize to 0 all remaining local variables
          let locals = S.toList $ MP.skScalars $ fnameSksMap M.! fname
              remLocals = locals \\ map getFargVar fargs
          initLocals <- mkInit0 sVarFunVec remLocals xp1
          -- Propagate all remaining variables
          propagate <- propvals locals
          mkAnd [params, initLocals, propagate]
        MP.Return fname fargs aargs -> do
          -- Assign result parameters
          let resArgs = map (\(MP.ValueResult r, MP.ActualValRes t) -> (r, t))
                $ filter (isValRes . fst) $ zip fargs aargs
              assign (r, t) = do
                txp1 <- mkApp1 (fst $ sVarFunVec V.! MP.varId t) xp1
                rx <- mkApp1 (fst $ sVarFunVec V.! MP.varId r) xLit
                mkEq txp1 rx
          params <- mkAndWith assign resArgs
          -- Restore remaining local variables (they may be overlapping if fname is recursive)
          let locals = S.toList $ MP.skScalars $ fnameSksMap M.! fname
              remLocals = locals \\ map snd resArgs
              restore s = do
                let sFunc = fst $ sVarFunVec V.! MP.varId s
                sxp1 <- mkApp1 sFunc xp1
                sPopped <- mkApp1 sFunc $ fromJust poppedNode
                mkEq sxp1 sPopped
          restoreLocals <- mkAndWith restore remLocals
          -- Propagate all remaining variables
          propagate <- propvals $ map snd resArgs ++ remLocals
          mkAnd [params, restoreLocals, propagate]
      where getFargVar (MP.Value var) = var
            getFargVar (MP.ValueResult var) = var
            isValRes (MP.ValueResult _) = True
            isValRes _ = False
            fnameSksMap = M.fromList $ map (\sk -> (MP.skName sk, sk)) $ MP.pSks prog

    evalBoolExpr :: Vector (FuncDecl, Sort) -> MP.Expr -> AST -> Z3 AST
    evalBoolExpr sVarFunVec g xLit = do
      bitSort <- mkBvSort 1
      true <- mkUnsignedInt 1 bitSort
      bvg <- mkBvredor =<< evalExpr sVarFunVec g xLit
      mkEq bvg true

    evalExpr :: Vector (FuncDecl, Sort) -> MP.Expr -> AST -> Z3 AST
    evalExpr sVarFunVec expr x = go expr where
      go e = case e of
        MP.Literal val     -> mkBitvector (BV.size val) (BV.nat val)
        MP.Term var        -> mkApp1 (fst $ sVarFunVec V.! MP.varId var) x
        MP.ArrayAccess _ _ -> error "Arrays not supported yet."
        MP.Not b           -> mkBvnot =<< mkBvredor =<< go b
        MP.And b1 b2       -> do
          b1x <- mkBvredor =<< go b1
          b2x <- mkBvredor =<< go b2
          mkBvand b1x b2x
        MP.Or b1 b2        -> do
          b1x <- mkBvredor =<< go b1
          b2x <- mkBvredor =<< go b2
          mkBvor b1x b2x
        MP.Add e1 e2       -> mkBinOp mkBvadd e1 e2
        MP.Sub e1 e2       -> mkBinOp mkBvsub e1 e2
        MP.Mul e1 e2       -> mkBinOp mkBvmul e1 e2
        MP.UDiv e1 e2      -> mkBinOp mkBvudiv e1 e2
        MP.SDiv e1 e2      -> mkBinOp mkBvsdiv e1 e2
        MP.URem e1 e2      -> mkBinOp mkBvurem e1 e2
        MP.SRem e1 e2      -> mkBinOp mkBvsrem e1 e2
        MP.Eq e1 e2        -> mkBvFromBool =<< mkBinOp mkEq e1 e2
        MP.ULt e1 e2       -> mkBvFromBool =<< mkBinOp mkBvult e1 e2
        MP.ULeq e1 e2      -> mkBvFromBool =<< mkBinOp mkBvule e1 e2
        MP.SLt e1 e2       -> mkBvFromBool =<< mkBinOp mkBvslt e1 e2
        MP.SLeq e1 e2      -> mkBvFromBool =<< mkBinOp mkBvsle e1 e2
        MP.UExt w e1       -> mkZeroExt w =<< go e1
        MP.SExt w e1       -> mkSignExt w =<< go e1
        MP.Trunc w e1      -> mkExtract (w - 1) 0 =<< go e1

      mkBinOp op e1 e2 = do
        e1x <- go e1
        e2x <- go e2
        op e1x e2x

      mkBvFromBool b = do
        bitSort <- mkBvSort 1
        true <- mkUnsignedInt 1 bitSort
        false <- mkUnsignedInt 0 bitSort
        mkIte b true false


-- push(x), shift(x), pop(x)
mkCheckPrec :: FuncDecl -> FuncDecl -> FuncDecl -> AST -> Z3 AST
mkCheckPrec smb struct precRel x = do
  smbX <- mkApp1 smb x
  structX <- mkApp1 struct x
  mkApp precRel [smbX, structX]


mkApp1 :: FuncDecl -> AST -> Z3 AST
mkApp1 f x = mkApp f [x]

mkAndWith :: (a -> Z3 AST) -> [a] -> Z3 AST
mkAndWith predGen items = mapM predGen items >>= mkAnd

mkOrWith :: (a -> Z3 AST) -> [a] -> Z3 AST
mkOrWith predGen items = mapM predGen items >>= mkOr

mkForallNodes :: [Word64] -> (Word64 -> Z3 AST) -> Z3 AST
mkForallNodes nodes predGen = mkAndWith predGen nodes

mkExistsNodes :: [Word64] -> (Word64 -> Z3 AST) -> Z3 AST
mkExistsNodes nodes predGen = mkOrWith predGen nodes


closure :: Alphabet MP.ExprProp -> Formula MP.ExprProp
        -> ([Formula MP.ExprProp], [Formula MP.ExprProp])
closure alphabet phi = (structClos, S.toList . S.fromList $ structClos ++ closList phi)
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

xnf :: Formula MP.ExprProp -> Formula MP.ExprProp
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
  Eventually _g   -> error "LTL operators only supported through translation."
  Always _g       -> error "LTL operators only supported through translation."
  AuxBack _ _     -> error "AuxBack not supported in SMT encoding."

translate :: Formula MP.ExprProp -> Formula MP.ExprProp
translate phi = fst $ transformFold applyTransl 0 phi where
  applyTransl :: Formula MP.ExprProp -> Word64 -> (Formula MP.ExprProp, Word64)
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
  mkUniqueProp n = Atomic . Prop . MP.TextProp . T.pack $ '@' : show n
  xOp Up psi = XBack Down psi `And` Not (XBack Up psi)
  xOp Down psi = XNext Up psi `And` Not (XNext Down psi)
  gammaLR dir qEta = xOp dir $ qEta
    `And` (ltlNext . Always . Not $ qEta)
    `And` (ltlBack . ltlPastAlways . Not $ qEta)


queryTableau :: Sort -> Map (Formula MP.ExprProp) AST
             -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
             -> Word64 -> Maybe Word64 -> Model -> Z3 [TableauNode]
queryTableau nodeSort fConstMap gamma smb stack ctx k maxLen model = do
  let unrollLength = case maxLen of
        Just ml -> min k ml
        Nothing -> k
  mapM queryTableauNode [1..unrollLength]
  where
    fConstList = M.toList fConstMap
    constPropMap = M.fromList $ map (\(Atomic p, fConst) -> (fConst, p))
                   $ filter (atomic . fst) fConstList
    queryTableauNode idx = do
      idxNode <- mkUnsignedInt64 idx nodeSort
      gammaVals <- filterM (\(_, fConst) -> fromJust <$>
                             (evalBool model =<< mkApp gamma [fConst, idxNode])) fConstList
      Just smbVal <- eval model =<< mkApp1 smb idxNode
      Just stackVal <- evalInt model =<< mkApp1 stack idxNode
      Just ctxVal <- evalInt model =<< mkApp1 ctx idxNode
      return TableauNode { nodeGammaC = map fst gammaVals
                         , nodeSmb = constPropMap M.! smbVal
                         , nodeStack = stackVal
                         , nodeCtx = ctxVal
                         , nodeIdx = fromIntegral idx
                         }
