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
import Pomc.Potl (Dir(..), Formula(..), pnf, atomic)
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
import Data.Bits (finiteBitSize, countLeadingZeros)

import qualified Debug.Trace as DBG

data SMTStatus = Sat | Unsat | Unknown deriving (Eq, Show)

data TableauNode a = TableauNode { nodeGammaC :: [Formula a]
                                 , nodeSmb    :: Prop a
                                 , nodeStack  :: Integer
                                 , nodeCtx    :: Integer
                                 , nodeIdx    :: Integer
                                 } deriving Eq

data SMTResult a = SMTResult { smtStatus :: SMTStatus
                             , smtTableau :: Maybe [TableauNode a]
                             , smtTimeAssert :: Double
                             , smtTimeCheck :: Double
                             , smtTimeModel :: Double
                             } deriving (Eq, Show)

instance Show a => Show (TableauNode a) where
  show tn = "(" ++ (intercalate ", " [ show $ nodeIdx tn
                                     , show $ nodeGammaC tn
                                     , "smb = " ++ show (nodeSmb tn)
                                     , "stack = " ++ show (nodeStack tn)
                                     , "ctx = " ++ show (nodeCtx tn)
                                     ]) ++ ")"


isSatisfiable :: (Eq a, Ord a, Show a)
              => Alphabet a
              -> Formula a
              -> Int
              -> IO (SMTResult a)
isSatisfiable alphabet phi maxDepth = evalZ3 $ incrementalCheck 0 0 1
  where
    incrementalCheck assertTime checkTime k
      | k > maxDepth = return SMTResult { smtStatus = Unknown
                                        , smtTableau = Nothing
                                        , smtTimeAssert = assertTime
                                        , smtTimeCheck = checkTime
                                        , smtTimeModel = 0
                                        }
      | otherwise = do
          reset
          (tableauQuery, newAssertTime) <-
            timeAction $ assertFormulaEncoding alphabet (pnf phi) k
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


assertFormulaEncoding :: forall a. (Show a, Eq a, Ord a)
                      => Alphabet a
                      -> Formula a
                      -> Int
                      -> Z3 (Maybe Int -> Model -> Z3 [TableauNode a])
assertFormulaEncoding alphabet phi k = do
  let kWidth = finiteBitSize k - countLeadingZeros k
  -- Sorts
  boolSort <- mkBoolSort
  nodeSort <- mkBvSort kWidth
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

  -- xnf(φ)(0)
  node0 <- mkInt 0 nodeSort
  assert =<< groundxnf fConstMap gamma (xnf phi) node0

  -- smb(0) = #
  smb0 <- mkApp1 smb node0
  assert =<< mkEq smb0 (fConstMap Map.! Atomic End)

  -- stack(0) = 0
  stack0 <- mkApp1 stack node0
  assert =<< mkEq stack0 node0

  -- ctx(0) = 0
  ctx0 <- mkApp1 ctx node0
  assert =<< mkEq ctx0 node0

  -- ∀x (...)
  xVar <- mkFreshConst "x" nodeSort
  xApp <- toApp xVar
  kVar <- mkInt k nodeSort

  -- x <= k
  xlek <- mkBvule xVar kVar
  endx <- mkEndTerm fConstMap gamma xVar
  conflictx <- mkConflict sSort sigma gamma xVar
  xlekImplies <- mkImplies xlek =<< mkAnd [endx, conflictx]

  -- x < k
  xltk <- mkBvult xVar kVar
  pnextx <- mkPnext nodeSort fConstMap gamma struct yield take xVar
  -- push(x) → PUSH(x)
  checkPushx <- mkCheckPrec smb struct yield xVar
  pushx <- mkPush nodeSort fConstMap gamma smb struct stack ctx yield equal take xVar
  pushxImpliesPushx <- mkImplies checkPushx pushx
  -- shift(x) → SHIFT(x)
  checkShiftx <- mkCheckPrec smb struct equal xVar
  shiftx <- mkShift nodeSort fConstMap gamma smb struct stack ctx xVar
  shiftxImpliesShiftx <- mkImplies checkShiftx shiftx
  -- pop(x) → POP(x)
  checkPopx <- mkCheckPrec smb struct take xVar
  popx <- mkPop sSort nodeSort gamma smb stack ctx xVar
  popxImpliesPopx <- mkImplies checkPopx popx

  xltkImplies <- mkImplies xltk =<< mkAnd [ pnextx
                                          , pushxImpliesPushx
                                          , shiftxImpliesShiftx
                                          , popxImpliesPopx
                                          ]
  assert =<< mkForallConst [] [xApp] =<< mkAnd [xlekImplies, xltkImplies]
  -- end ∀x (...)

  -- EMPTY(k)
  assert =<< mkEmpty nodeSort fConstMap gamma stack kVar
  -- k > 0
  return $ queryTableau nodeSort fConstMap gamma smb stack ctx kVar
  where
    (structClos, clos) = closure alphabet phi

    mkSSort :: Z3 (Sort, Map (Formula a) AST)
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

    mkPhiAxioms :: Sort -> Map (Formula a) AST
                -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> Z3 AST
    mkPhiAxioms nodeSort fConstMap sigma struct smb gamma = do
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- mkAndWith (mkApp1 sigma . (fConstMap Map.!)) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- mkAndWith (mkNot <=< mkApp1 sigma . (fConstMap Map.!))
                            (clos \\ structClos)
      -- ∀x(Σ(struct(x)) ∧ Σ(smb(x)) ∧ Γ(struct(x), x))
      xVar <- mkFreshConst "x" nodeSort
      xApp <- toApp xVar
      structX <- mkApp1 struct xVar
      sigmaStructX <- mkApp1 sigma structX
      sigmaSmbX    <- mkApp1 sigma =<< mkApp1 smb xVar
      gammaStructXX <- mkApp gamma [structX, xVar]
      forall <- mkForallConst [] [xApp] =<< mkAnd [sigmaStructX, sigmaSmbX, gammaStructXX]
      mkAnd [allStructInSigma, allOtherNotInSigma, forall]

    mkPhiOPM :: Map (Formula a) AST -> FuncDecl -> FuncDecl -> FuncDecl -> Z3 AST
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
    groundxnf :: Map (Formula a) AST -> FuncDecl -> Formula a -> AST -> Z3 AST
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
    mkEndTerm :: Map (Formula a) AST -> FuncDecl -> AST -> Z3 AST
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
    mkPnext :: Sort -> Map (Formula a) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> AST
            -> Z3 AST
    mkPnext nodeSort fConstMap gamma struct yield take x = do
      let pnextPrec prec g = do
            -- Γ(g, x)
            gammagx <- mkApp gamma [fConstMap Map.! g, x]
            -- struct(x) prec struct(x + 1)
            structx <- mkApp1 struct x
            xp1 <- mkBvadd x =<< mkInt 1 nodeSort
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
    mkPush :: Sort -> Map (Formula a) AST
           -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
           -> FuncDecl -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkPush nodeSort fConstMap gamma smb struct stack ctx yield equal take x = do
      let mxp1 = mkBvadd x =<< mkInt 1 nodeSort
          propagateNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap Map.! next, x]
            rhs <- groundxnf fConstMap gamma (xnf arg) =<< mxp1
            mkEq lhs rhs
      -- big ands
      pnextRule <- mkAndWith propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- mkAndWith propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      xp1 <- mxp1
      smbxp1 <- mkApp1 smb xp1
      structx <- mkApp1 struct x
      smbRule <- mkEq smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- mkApp1 stack xp1
      stackRule <- mkEq stackxp1 x
      -- stack(x) = 0 → ctx(x + 1) = 0
      node0 <- mkInt 0 nodeSort
      stackx <- mkApp1 stack x
      ctxxp1 <- mkApp1 ctx xp1
      stackxEq0 <- mkEq stackx node0
      ctxxp1Eq0 <- mkEq ctxxp1 node0
      rootCtxRule <- mkImplies stackxEq0 ctxxp1Eq0
      -- (stack(x) != 0 ∧ (push(x − 1) ∨ shift(x − 1))) → ctx(x + 1) = x − 1
      stackxNeq0 <- mkNot =<< mkEq stackx node0
      xm1 <- mkBvsub x =<< mkInt 1 nodeSort
      pushxm1 <- mkCheckPrec smb struct yield xm1
      shiftxm1 <- mkCheckPrec smb struct equal xm1
      pushOrShiftxm1 <- mkOr [pushxm1, shiftxm1]
      stackxNeq0AndpushOrShiftxm1 <- mkAnd [stackxNeq0, pushOrShiftxm1]
      ctxxp1Eqxm1 <- mkEq ctxxp1 xm1
      pushShiftCtxRule <- mkImplies stackxNeq0AndpushOrShiftxm1 ctxxp1Eqxm1
      -- (stack(x) != 0 ∧ pop(x − 1)) → ctx(x + 1) = ctx(x)
      popxm1 <- mkCheckPrec smb struct take xm1
      stackxNeq0AndPopxm1 <- mkAnd [stackxNeq0, popxm1]
      ctxx <- mkApp1 ctx x
      ctxxp1Eqctxx <- mkEq ctxxp1 ctxx
      popCtxRule <- mkImplies stackxNeq0AndPopxm1 ctxxp1Eqctxx
      -- Final and
      mkAnd [ pnextRule, wpnextRule
            , smbRule, stackRule
            , rootCtxRule, pushShiftCtxRule, popCtxRule
            ]

    -- SHIFT(x)
    mkShift :: Sort -> Map (Formula a) AST
            -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
            -> AST -> Z3 AST
    mkShift nodeSort fConstMap gamma smb struct stack ctx x = do
      let mxp1 = mkBvadd x =<< mkInt 1 nodeSort
          propagateNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap Map.! next, x]
            rhs <- groundxnf fConstMap gamma (xnf arg) =<< mxp1
            mkImplies lhs rhs
      -- big ands
      pnextRule <- mkAndWith propagateNext [(g, alpha) | g@(PNext _ alpha) <- clos]
      wpnextRule <- mkAndWith propagateNext [(g, alpha) | g@(WPNext _ alpha) <- clos]
      -- smb(x + 1) = struct(x)
      xp1 <- mxp1
      smbxp1 <- mkApp1 smb xp1
      structx <- mkApp1 struct x
      smbRule <- mkEq smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- mkApp1 stack xp1
      stackx <- mkApp1 stack x
      stackRule <- mkEq stackxp1 stackx
      -- ctx(x + 1) = ctx(x)
      ctxxp1 <- mkApp1 ctx xp1
      ctxx <- mkApp1 ctx x
      ctxRule <- mkEq ctxxp1 ctxx
      -- Final and
      mkAnd [pnextRule, wpnextRule, smbRule, stackRule, ctxRule]

    -- POP(xExpr)
    mkPop :: Sort -> Sort -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkPop sSort nodeSort gamma smb stack ctx x = do
      xp1 <- mkBvadd x =<< mkInt 1 nodeSort
      -- ∀p(Γ(p, x) ↔ Γ(p, x + 1))
      pVar <- mkFreshConst "p" sSort
      pApp <- toApp pVar
      gammapx <- mkApp gamma [pVar, x]
      gammapxp1 <- mkApp gamma [pVar, xp1]
      gammaIff <- mkIff gammapx gammapxp1
      gammaRule <- mkForallConst [] [pApp] gammaIff
      -- smb(x + 1) = smb(stack(x))
      smbxp1 <- mkApp1 smb xp1
      stackx <- mkApp1 stack x
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
    mkEmpty :: Sort -> Map (Formula a) AST -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkEmpty nodeSort fConstMap gamma stack x = do
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap Map.! Atomic End, x]
      -- stack(x) = 0
      stackx <- mkApp1 stack x
      stackxEq0 <- mkEq stackx =<< mkInt 0 nodeSort
      mkAnd [gammaEndx, stackxEq0]


mkApp1 :: FuncDecl -> AST -> Z3 AST
mkApp1 f x = mkApp f [x]


mkAndWith :: (a -> Z3 AST) -> [a] -> Z3 AST
mkAndWith predGen items = mapM predGen items >>= mkAnd


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


queryTableau :: Sort -> Map (Formula a) AST
             -> FuncDecl -> FuncDecl -> FuncDecl -> FuncDecl
             -> AST -> Maybe Int -> Model -> Z3 [TableauNode a]
queryTableau nodeSort fConstMap gamma smb stack ctx kVar maxLen model = do
  -- DBG.traceM =<< showModel model
  Just kVal <- fmap fromInteger <$> evalBv False model kVar
  let unrollLength = case maxLen of
        Just ml -> min kVal ml
        Nothing -> kVal
  mapM queryTableauNode [0..unrollLength]
  where
    fConstList = Map.toList fConstMap
    constPropMap = Map.fromList $ map (\(Atomic p, fConst) -> (fConst, p))
                   $ filter (atomic . fst) fConstList
    queryTableauNode idx = do
      idxNode <- mkInt idx nodeSort
      gammaVals <- filterM (\(_, fConst) -> fromJust <$>
                             (evalBool model =<< mkApp gamma [fConst, idxNode])) fConstList
      Just smbVal <- eval model =<< mkApp1 smb idxNode
      Just stackVal <- evalBv False model =<< mkApp1 stack idxNode
      Just ctxVal <- evalBv False model =<< mkApp1 ctx idxNode
      return TableauNode { nodeGammaC = map fst gammaVals
                         , nodeSmb = constPropMap Map.! smbVal
                         , nodeStack = stackVal
                         , nodeCtx = ctxVal
                         , nodeIdx = fromIntegral idx
                         }
