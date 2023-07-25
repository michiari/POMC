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

import Prelude hiding (take, pred)

import Pomc.Prop (Prop(..))
import Pomc.Potl (Dir(..), Formula(..), pnf, atomic)
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
    pnfPhi = pnf phi
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
          -- (res, newCheckTime) <- timeAction $ solverCheck
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

data EncData = EncData { zNodeSort  :: Sort
                       , zSSort     :: Sort
                       , zFConstMap :: Map (Formula MP.ExprProp) AST
                       , zGamma     :: FuncDecl
                       , zSigma     :: FuncDecl
                       , zStruct    :: FuncDecl
                       , zSmb       :: FuncDecl
                       , zYield     :: FuncDecl
                       , zEqual     :: FuncDecl
                       , zTake      :: FuncDecl
                       , zStack     :: FuncDecl
                       , zCtx       :: FuncDecl
                       , zPred      :: FuncDecl
                       }

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
  sigma  <- mkFreshFuncDecl "sigma" [sSort] boolSort -- TODO: try & remove sigma
  struct <- mkFreshFuncDecl "struct" [nodeSort] sSort
  smb    <- mkFreshFuncDecl "smb" [nodeSort] sSort
  yield  <- mkFreshFuncDecl "yield" [sSort, sSort] boolSort
  equal  <- mkFreshFuncDecl "equal" [sSort, sSort] boolSort
  take   <- mkFreshFuncDecl "take" [sSort, sSort] boolSort
  stack  <- mkFreshFuncDecl "stack" [nodeSort] nodeSort
  ctx    <- mkFreshFuncDecl "ctx" [nodeSort] nodeSort
  pred   <- mkFreshFuncDecl "pred" [nodeSort] nodeSort
  -- Auxiliary encoding struct
  let encData = EncData
        { zNodeSort  = nodeSort
        , zSSort     = sSort
        , zFConstMap = fConstMap
        , zGamma     = gamma
        , zSigma     = sigma
        , zStruct    = struct
        , zSmb       = smb
        , zYield     = yield
        , zEqual     = equal
        , zTake      = take
        , zStack     = stack
        , zCtx       = ctx
        , zPred      = pred
        }
  -- Encoding
  assert =<< mkPhiAxioms encData
  assert =<< mkPhiOPM encData

  -- struct(⊥) = smb(⊥) = #
  nodeBot <- mkUnsignedInt64 0 nodeSort -- Note: all quantifiers on nodes should exclude 0
  assert =<< mkEq (fConstMap M.! Atomic End) =<< mkApp1 struct nodeBot
  assert =<< mkEq (fConstMap M.! Atomic End) =<< mkApp1 smb nodeBot

  -- xnf(φ)(1)
  node1 <- mkUnsignedInt64 1 nodeSort
  assert =<< groundxnf encData phi node1

  -- smb(1) = #
  assert =<< mkEq (fConstMap M.! Atomic End) =<< mkApp1 smb node1

  -- stack(1) = ⊥
  assert =<< mkEq nodeBot =<< mkApp1 stack node1

  -- ctx(1) = ⊥
  assert =<< mkEq nodeBot =<< mkApp1 ctx node1

  -- Back is false and WBack is true in 1
  let holdsIn1 g = mkApp gamma [fConstMap M.! g, node1]
  assert =<< mkAndWith (mkNot <=< holdsIn1) [g | g@(Back _) <- clos]
  assert =<< mkAndWith holdsIn1 [g | g@(WBack _) <- clos]

  -- start ∀x (...)
  -- x <= k
  let mkTermRules x = do
        xLit <- mkUnsignedInt64 x nodeSort
        checkPushx <- mkCheckPrec encData yield xLit
        checkShiftx <- mkCheckPrec encData equal xLit
        checkPopx <- mkCheckPrec encData take xLit
        inputx <- mkOr [checkPushx, checkShiftx]
        -- xnextx
        inputxImpliesXnextx <- mkImplies inputx =<< mkXnext encData x
        -- wxnextx
        popxImpliesWxnextx <- mkImplies checkPopx =<< mkWxnext encData x
        -- whnextu
        whnextux <- mkWhnextu encData x checkPopx
        -- whnextd
        whnextdx <- mkWhnextd encData x checkPopx
        -- huaux
        huauxx <- mkHuaux encData x checkPushx checkPopx
        endx <- mkEndTerm fConstMap gamma xLit
        conflictx <- mkConflict fConstMap gamma struct xLit
        mkAnd [ inputxImpliesXnextx, popxImpliesWxnextx
              , whnextux, whnextdx, huauxx
              , endx, conflictx
              ]
  assert =<< mkForallNodes [1..k] mkTermRules

  -- x < k
  let mkTransitions x = do
        xLit <- mkUnsignedInt64 x nodeSort
        checkPushx <- mkCheckPrec encData yield xLit
        checkShiftx <- mkCheckPrec encData equal xLit
        checkPopx <- mkCheckPrec encData take xLit
        inputx <- mkOr [checkPushx, checkShiftx]
        -- push(x) → PUSH(x)
        pushxImpliesPushx <- mkImplies checkPushx =<< mkPush encData x
        -- shift(x) → SHIFT(x)
        shiftxImpliesShiftx <- mkImplies checkShiftx =<< mkShift encData x
        -- pop(x) → POP(x)
        popxImpliesPopx <- mkImplies checkPopx =<< mkPop encData x
        -- pnextx
        inputxImpliesPnextx <- mkImplies inputx =<< mkPnext encData x
        -- hnextu
        hnextux <- mkHnextu encData x checkPushx checkPopx
        -- hnextd
        hnextdx <- mkHnextd encData x checkPopx
        -- hdaux
        hdauxx <- mkHdaux encData x checkPopx
        mkAnd [ pushxImpliesPushx, shiftxImpliesShiftx, popxImpliesPopx
              , inputxImpliesPnextx, hnextux, hnextdx, hdauxx
              ]
  assert =<< mkForallNodes [1..(k - 1)] mkTransitions
  -- end ∀x (...)

  -- EMPTY(k)
  assert =<< mkEmpty nodeSort fConstMap gamma stack k

  case query of
    SatQuery _ -> return ()
    MiniProcQuery prog ->
      encodeProg encData nodeSort fConstMap gamma struct yield equal take stack prog k

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

    mkPhiAxioms :: EncData -> Z3 AST
    mkPhiAxioms encData = do
      let fConstMap = zFConstMap encData
          sigma = zSigma encData
      -- ∧_(p∈Σ) Σ(p)
      allStructInSigma <- mkAndWith (mkApp1 sigma . (fConstMap M.!)) structClos
      -- ∧_(p∈S \ Σ) ¬Σ(p)
      allOtherNotInSigma <- mkAndWith (mkNot <=< mkApp1 sigma . (fConstMap M.!))
                            (clos \\ structClos)
      -- ∀x(Σ(struct(x)) ∧ Σ(smb(x)) ∧ Γ(struct(x), x))
      forall <- mkAndWith (\x -> do
                              xLit <- mkUnsignedInt64 x $ zNodeSort encData
                              structX <- mkApp1 (zStruct encData) xLit
                              sigmaStructX <- mkApp1 sigma structX
                              sigmaSmbX    <- mkApp1 sigma =<< mkApp1 (zSmb encData) xLit
                              gammaStructXX <- mkApp (zGamma encData) [structX, xLit]
                              mkAnd [sigmaStructX, sigmaSmbX, gammaStructXX]
                          ) [1..k]
      mkAnd [allStructInSigma, allOtherNotInSigma, forall]

    mkPhiOPM :: EncData -> Z3 AST
    mkPhiOPM encData = E.assert (isComplete alphabet)
      $ mkAndWith assertPrecPair
      $ snd alphabet ++ (End, End, Equal):[(End, p, Yield) | p <- fst alphabet]
      where assertPrecPair (p, q, prec) = do
              let fConstMap = zFConstMap encData
                  pqArg = [fConstMap M.! Atomic p, fConstMap M.! Atomic q]
                  (nPrec1, nPrec2) = getNegPrec prec
              posPrec  <- mkApp (getPosPrec prec) pqArg
              negPrec1 <- mkNot =<< mkApp nPrec1 pqArg
              negPrec2 <- mkNot =<< mkApp nPrec2 pqArg
              mkAnd [posPrec, negPrec1, negPrec2]

            (yield, equal, take) = (zYield encData, zEqual encData, zTake encData)

            getPosPrec Yield = yield
            getPosPrec Equal = equal
            getPosPrec Take = take

            getNegPrec Yield = (equal, take)
            getNegPrec Equal = (yield, take)
            getNegPrec Take = (yield, equal)

    -- xnf(theta)_G(x)
    groundxnf :: EncData -> Formula MP.ExprProp -> AST -> Z3 AST
    groundxnf encData theta x = ground (xnf theta) where
      ground f = case f of
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
        HNext _ _        -> applyGamma f
        HBack _ _        -> error "Hierarchical operators not supported yet."
        WHNext _ _       -> applyGamma f
        Until _ _ _      -> error "Supplied formula is not in Next Normal Form."
        Release _ _ _    -> error "Supplied formula is not in Next Normal Form."
        Since _ _ _      -> error "Past operators not supported yet."
        HUntil _ _ _     -> applyGamma f
        HRelease _ _ _   -> applyGamma f
        HSince _ _ _     -> error "Supplied formula is not in Next Normal Form."
        Next _           -> applyGamma f
        WNext _          -> applyGamma f
        Back _           -> applyGamma f
        WBack _          -> applyGamma f
        Eventually _     -> error "Supplied formula is not in Next Normal Form."
        Always _         -> error "Supplied formula is not in Next Normal Form."
        Once _           -> error "Supplied formula is not in Next Normal Form."
        Historically _   -> error "Supplied formula is not in Next Normal Form."
        AuxBack _ _      -> error "AuxBack not supported in SMT encoding."
        where boolPred op lhs rhs = do
                glhs <- ground lhs
                grhs <- ground rhs
                op glhs grhs

              applyGamma g = mkApp (zGamma encData) [zFConstMap encData M.! g, x]

    -- END(xExpr)
    mkEndTerm :: Map (Formula MP.ExprProp) AST -> FuncDecl -> AST -> Z3 AST
    mkEndTerm fConstMap gamma x = do
      let noGamma g = mkNot =<< mkApp gamma [fConstMap M.! g, x]
      -- Γ(#, x)
      gammaEndx <- mkApp gamma [fConstMap M.! Atomic End, x]
      -- ∧_(PNext t α ∈ Cl(φ)) ¬Γ((PNext t α)_G, x)
      noGammaPNext <- mkAndWith noGamma [g | g@(PNext _ _) <- clos]
      -- ∧_(Next α ∈ Cl(φ)) ¬Γ((Next α)_G, x)
      noGammaNext <- mkAndWith noGamma [g | g@(Next _) <- clos]
      -- ∧_(HNext t α ∈ Cl(φ)) ¬Γ((HNext t α)_G, x)
      noGammaHNext <- mkAndWith noGamma [g | g@(HNext _ _) <- clos]
      -- ∧_(p ∈ AP) ¬Γ(p, x)
      noGammaAP <- mkAndWith noGamma [g | g@(Atomic (Prop _)) <- clos]
      noGammaAll <- mkAnd [noGammaPNext, noGammaNext, noGammaHNext, noGammaAP]
      -- Final →
      mkImplies gammaEndx noGammaAll

    -- CONFLICT(x)
    mkConflict :: Map (Formula MP.ExprProp) AST -> FuncDecl -> FuncDecl -> AST -> Z3 AST
    mkConflict fConstMap gamma struct x = do
      structx <- mkApp1 struct x
      let singleSl p = do
            structxEqp <- mkEq structx (fConstMap M.! p)
            noOtherSls <- mkAndWith (\q -> mkNot =<< mkApp gamma [fConstMap M.! q, x])
                          $ filter (/= p) structClos
            mkAnd [structxEqp, noOtherSls]
      mkOrWith singleSl structClos


    -- PNEXT(x) ∧ WPNEXT(x)
    mkPnext :: EncData -> Word64 -> Z3 AST
    mkPnext encData x = do
      let fConstMap = zFConstMap encData
          gamma = zGamma encData
          struct = zStruct encData
      xLit <- mkUnsignedInt64 x $ zNodeSort encData
      xp1 <- mkUnsignedInt64 (x + 1) $ zNodeSort encData
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
      pnextDown <- mkAndWith (pnextPrec $ zTake encData) [g | g@(PNext Down _) <- clos]
      -- ∧_(PNext u α ∈ Cl(φ)) (...)
      pnextUp <- mkAndWith (pnextPrec $ zYield encData) [g | g@(PNext Up _) <- clos]
      let wpnextPrec prec (g, arg) = do
            -- Γ(g, x)
            gammagx <- mkApp gamma [fConstMap M.! g, xLit]
            -- Γ(h, x + 1)
            gammahxp1 <- groundxnf encData arg xp1
            -- struct(x) prec struct(x + 1)
            structx <- mkApp1 struct xLit
            structxp1 <- mkApp1 struct xp1
            structPrec <- mkApp prec [structx, structxp1]
            -- Final implication
            notStructPrec <- mkNot structPrec
            gammagxAndNotStructPrec <- mkAnd [gammagx, notStructPrec]
            mkImplies gammagxAndNotStructPrec gammahxp1
      wpnextDown <- mkAndWith (wpnextPrec $ zTake encData) [(g, arg) | g@(WPNext Down arg) <- clos]
      wpnextUp <- mkAndWith (wpnextPrec $ zYield encData) [(g, arg) | g@(WPNext Up arg) <- clos]
      mkAnd [pnextDown, pnextUp, wpnextDown, wpnextUp]

    -- XNEXT(x)
    mkXnext :: EncData -> Word64 -> Z3 AST
    mkXnext encData x = do
      let nodeSort = zNodeSort encData
          struct = zStruct encData
      xLit <- mkUnsignedInt64 x nodeSort
      structx <- mkApp1 struct xLit
      let xnextSat g@(XNext dir arg) = do
            gammagx <- mkApp (zGamma encData) [zFConstMap encData M.! g, xLit]
            let satisfied z = do
                  zLit <- mkUnsignedInt64 z nodeSort
                  checkPopz <- mkCheckPrec encData (zTake encData) zLit
                  ctxz <- mkApp1 (zCtx encData) zLit
                  ctxzEqx <- mkEq ctxz xLit
                  xnfArgz <- groundxnf encData arg zLit
                  structz <- mkApp1 struct zLit
                  precYT <- case dir of
                    Down -> mkApp (zYield encData) [structx, structz]
                    Up   -> mkApp (zTake encData) [structx, structz]
                  precEq <- mkApp (zEqual encData) [structx, structz]
                  orPrec <- mkOr [precYT, precEq]
                  mkAnd [checkPopz, ctxzEqx, xnfArgz, orPrec]
            exists <- mkExistsNodes [x..k] satisfied
            -- Implies
            mkImplies gammagx exists
          xnextSat _ = error "XNext formula expected."
      mkAndWith xnextSat [g | g@(XNext _ _) <- clos]

    mkWxnext :: EncData -> Word64 -> Z3 AST
    mkWxnext encData x = do
      let struct = zStruct encData
      xLit <- mkUnsignedInt64 x $ zNodeSort encData
      structx <- mkApp1 struct xLit
      ctxx <- mkApp1 (zCtx encData) xLit
      structCtxx <- mkApp1 struct ctxx
      let wxnextSat g@(WXNext dir arg) = do
            gammagctxx <- mkApp (zGamma encData) [zFConstMap encData M.! g, ctxx]
            precYT <- case dir of
              Down -> mkApp (zYield encData) [structCtxx, structx]
              Up   -> mkApp (zTake encData) [structCtxx, structx]
            precEq <- mkApp (zEqual encData) [structCtxx, structx]
            orPrec <- mkOr [precYT, precEq]
            gammagctxxAndOrPrec <- mkAnd [gammagctxx, orPrec]
            xnfArgx <- groundxnf encData arg xLit
            mkImplies gammagctxxAndOrPrec xnfArgx
      mkAndWith wxnextSat [g | g@(WXNext _ _) <- clos]

    mkHnextu :: EncData -> Word64 -> AST -> AST -> Z3 AST
    mkHnextu encData x checkPushx checkPopx =
      let allHnu = [g | g@(HNext Up _) <- clos]
      in enableIf (not $ null allHnu) $ do
        let nodeSort = zNodeSort encData
        xLit <- mkUnsignedInt64 x nodeSort
        stackx <- mkApp1 (zStack encData) xLit
        xp1 <- mkUnsignedInt64 (x + 1) nodeSort
        checkPushxp1 <- mkCheckPrec encData (zYield encData) xp1
        let hnextuSat g@(HNext Up arg) = do
              gammagstackx <- mkApp (zGamma encData) [zFConstMap encData M.! g, stackx]
              xnfArgx <- groundxnf encData arg xLit
              mkImplies gammagstackx =<< mkAnd [xnfArgx, checkPushxp1]
        allHnextuSat <- mkAndWith hnextuSat allHnu
        popxImplies <- mkImplies checkPopx allHnextuSat

        hucond <- mkHUCond encData x checkPushx checkPopx allHnu
        mkAnd [popxImplies, hucond]

    mkWhnextu :: EncData -> Word64 -> AST -> Z3 AST
    mkWhnextu encData x checkPopx =
      let allWhnu = [g | g@(WHNext Up _) <- clos]
      in enableIf (not $ null allWhnu) $ do
        let nodeSort = zNodeSort encData
            struct = zStruct encData
            yield = zYield encData
            pred = zPred encData
        xLit <- mkUnsignedInt64 x nodeSort
        predx <- mkApp1 pred xLit
        xm1 <- mkUnsignedInt64 (x - 1) nodeSort
        predxEqxm1 <- mkEq predx xm1

        stackx <- mkApp1 (zStack encData) xLit
        checkPushStackx <- mkCheckPrec encData yield stackx
        stackxm1 <- mkApp1 pred stackx
        checkPopStackxm1 <- mkCheckPrec encData (zTake encData) stackxm1

        structx <- mkApp1 struct xLit
        ctxx <- mkApp1 (zCtx encData) xLit
        structCtxx <- mkApp1 struct ctxx
        precY <- mkApp yield [structCtxx, structx]

        implLhs <- mkAnd [checkPopx, checkPushStackx, checkPopStackxm1, precY]

        let whnextuSat g@(WHNext Up arg) = do
              gammagStackx <- mkApp (zGamma encData) [zFConstMap encData M.! g, stackx]
              xnfArgx <- groundxnf encData arg xLit
              mkImplies gammagStackx xnfArgx
        allWhnextuSat <- mkImplies implLhs =<< mkAndWith whnextuSat allWhnu
        mkAnd [predxEqxm1, allWhnextuSat]

    mkHnextd :: EncData -> Word64 -> AST -> Z3 AST
    mkHnextd encData x checkPopx =
      let allHnd = [g | g@(HNext Down _) <- clos]
      in enableIf (not $ null allHnd) $ do
        let nodeSort = zNodeSort encData
            ctx = zCtx encData
        xLit <- mkUnsignedInt64 x nodeSort
        ctxx <- mkApp1 ctx xLit
        xm1 <- mkUnsignedInt64 (x - 1) nodeSort
        ctxxm1 <- mkApp1 ctx xm1
        checkPopxm1 <- mkCheckPrec encData (zTake encData) xm1
        let hnextdSat g@(HNext Down arg) = do
              gammagCtxx <- mkApp (zGamma encData) [zFConstMap encData M.! g, ctxx]
              xnfArgCtxxm1 <- groundxnf encData arg ctxxm1
              mkImplies gammagCtxx =<< mkAnd [xnfArgCtxxm1, checkPopxm1]
        popImpl <- mkImplies checkPopx =<< mkAndWith hnextdSat allHnd
        hdcond <- mkHDCond encData x checkPopx allHnd
        mkAnd [popImpl, hdcond]

    mkWhnextd :: EncData -> Word64 -> AST -> Z3 AST
    mkWhnextd encData x checkPopx =
      let allWhnd = [g | g@(WHNext Down _) <- clos]
      in enableIf (not $ null allWhnd) $ do
        let nodeSort = zNodeSort encData
            ctx = zCtx encData
            take = zTake encData
        xLit <- mkUnsignedInt64 x nodeSort
        structx <- mkApp1 (zStruct encData) xLit
        stackx <- mkApp1 (zStack encData) xLit
        ctxx <- mkApp1 ctx xLit
        xm1 <- mkUnsignedInt64 (x - 1) nodeSort
        checkPopxm1 <- mkCheckPrec encData take xm1
        ctxxm1 <- mkApp1 ctx xm1
        smbStackx <- mkApp1 (zSmb encData) stackx
        checkPopxp1 <- mkApp take [smbStackx, structx]
        lhs <- mkAnd [checkPopx, checkPopxm1, checkPopxp1]
        let whnextdSat g@(WHNext Down arg) = do
              gammagCtxx <- mkApp (zGamma encData) [zFConstMap encData M.! g, ctxx]
              xnfArgCtxxm1 <- groundxnf encData arg ctxxm1
              mkImplies gammagCtxx xnfArgCtxxm1
        mkImplies lhs =<< mkAndWith whnextdSat allWhnd

    mkHuaux :: EncData -> Word64 -> AST -> AST -> Z3 AST
    mkHuaux encData x checkPushx checkPopx = enableIf (HUntil Up T T `elem` clos) $ do
      let nodeSort = zNodeSort encData
      xm1 <- mkUnsignedInt64 (x - 1) nodeSort
      checkPopxm1 <- mkCheckPrec encData (zTake encData) xm1
      whenNotPop <- mkAnd [checkPushx, checkPopxm1]
      hucond <- mkOr [checkPopx, whenNotPop]

      xLit <- mkUnsignedInt64 x nodeSort
      huaux <- mkApp (zGamma encData) [zFConstMap encData M.! HUntil Up T T, xLit]
      huauxImplies <- mkImplies huaux hucond

      impliesHuaux <- mkImplies whenNotPop huaux
      mkAnd [huauxImplies, impliesHuaux]

    mkHdaux :: EncData -> Word64 -> AST -> Z3 AST
    mkHdaux encData x checkPopx = enableIf (HUntil Down T T `elem` clos) $ do
      let nodeSort = zNodeSort encData
      xLit <- mkUnsignedInt64 x nodeSort
      ctxx <- mkApp1 (zCtx encData) xLit
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      checkPopxp1 <- mkCheckPrec encData (zTake encData) xp1
      popxAndPopxp1 <- mkAnd [checkPopx, checkPopxp1]
      hdaux <- mkApp (zGamma encData) [zFConstMap encData M.! HUntil Down T T, ctxx]
      impliesHdaux <- mkImplies popxAndPopxp1 hdaux
      hdcond <- mkHDCond encData x checkPopx [HUntil Down T T]
      mkAnd [impliesHdaux, hdcond]

    mkHUCond :: EncData -> Word64 -> AST -> AST -> [Formula MP.ExprProp] -> Z3 AST
    mkHUCond encData x checkPushx checkPopx allOps = do
      let nodeSort = zNodeSort encData
      xm1 <- mkUnsignedInt64 (x - 1) nodeSort
      checkPopxm1 <- mkCheckPrec encData (zTake encData) xm1
      whenNotPop <- mkAnd [checkPushx, checkPopxm1]
      hucond <- mkOr [checkPopx, whenNotPop]

      xLit <- mkUnsignedInt64 x nodeSort
      anyOpsx <- mkOrWith (\g -> mkApp (zGamma encData) [zFConstMap encData M.! g, xLit]) allOps
      mkImplies anyOpsx hucond

    mkHDCond :: EncData -> Word64 -> AST -> [Formula MP.ExprProp] -> Z3 AST
    mkHDCond encData x checkPopx allOps = do
      let nodeSort = zNodeSort encData
          fConstMap = zFConstMap encData
          gamma = zGamma encData
      xLit <- mkUnsignedInt64 x nodeSort
      notPopx <- mkNot checkPopx
      anyOpsx <- mkOrWith (\g -> mkApp gamma [fConstMap M.! g, xLit]) allOps
      notPopxAndAnyOpsx <- mkAnd [notPopx, anyOpsx]
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      checkPushxp1 <- mkCheckPrec encData (zYield encData) xp1
      notPopImpl <- mkImplies notPopxAndAnyOpsx checkPushxp1

      ctxx <- mkApp1 (zCtx encData) xLit
      anyOpsCtxx <- mkOrWith (\g -> mkApp gamma [fConstMap M.! g, ctxx]) allOps
      popxAndAnyOpsCtxx <- mkAnd [checkPopx, anyOpsCtxx]
      checkPopxp1 <- mkCheckPrec encData (zTake encData) xp1
      popImpl <- mkImplies popxAndAnyOpsCtxx checkPopxp1

      mkAnd [notPopImpl, popImpl]

    mkNextBackRules :: EncData -> Word64 -> Z3 AST
    mkNextBackRules encData x = do
      let nodeSort = zNodeSort encData
          fConstMap = zFConstMap encData
          gamma = zGamma encData
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      -- PNext, Next and WNext
      let propagateNext (next, arg) = do
            lhs <- mkApp gamma [fConstMap M.! next, xLit]
            rhs <- groundxnf encData arg xp1
            mkImplies lhs rhs
      -- big and
      nextRule <- mkAndWith propagateNext
        ([(g, alpha) | g@(PNext _ alpha) <- clos]
         ++ [(g, alpha) | g@(Next alpha) <- clos]
         ++ [(g, alpha) | g@(WNext alpha) <- clos])
      -- Back and WBack
      let propagateBack (back, arg) = do
            lhs <- mkApp gamma [fConstMap M.! back, xp1]
            rhs <- groundxnf encData arg xLit
            mkImplies lhs rhs
      -- big and
      backRule <- mkAndWith propagateBack
        ([(g, alpha) | g@(Back alpha) <- clos]
         ++ [(g, alpha) | g@(WBack alpha) <- clos])
      mkAnd [nextRule, backRule]

    -- PUSH(x)
    mkPush :: EncData -> Word64 -> Z3 AST
    mkPush encData x = do
      let nodeSort = zNodeSort encData
      -- Propagate Next and Back operators
      nextBackRules <- mkNextBackRules encData x
      -- Bookkeeping functions
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      -- smb(x + 1) = struct(x)
      smbxp1 <- mkApp1 (zSmb encData) xp1
      structx <- mkApp1 (zStruct encData) xLit
      smbRule <- mkEq smbxp1 structx
      -- stack(x + 1) = x
      stackxp1 <- mkApp1 (zStack encData) xp1
      stackRule <- mkEq stackxp1 xLit
      -- stack(x) = ⊥ → ctx(x + 1) = ⊥
      nodeBot <- mkUnsignedInt64 0 nodeSort
      stackx <- mkApp1 (zStack encData) xLit
      ctxxp1 <- mkApp1 (zCtx encData) xp1
      stackxEqBot <- mkEq stackx nodeBot
      ctxxp1EqBot <- mkEq ctxxp1 nodeBot
      botCtxRule <- mkImplies stackxEqBot ctxxp1EqBot
      -- (stack(x) != ⊥ ∧ (push(x − 1) ∨ shift(x − 1))) → ctx(x + 1) = x − 1
      stackxNeqBot <- mkNot =<< mkEq stackx nodeBot
      xm1 <- mkUnsignedInt64 (x - 1) nodeSort
      pushxm1 <- mkCheckPrec encData (zYield encData) xm1
      shiftxm1 <- mkCheckPrec encData (zEqual encData) xm1
      pushOrShiftxm1 <- mkOr [pushxm1, shiftxm1]
      stackxNeqBotAndpushOrShiftxm1 <- mkAnd [stackxNeqBot, pushOrShiftxm1]
      ctxxp1Eqxm1 <- mkEq ctxxp1 xm1
      pushShiftCtxRule <- mkImplies stackxNeqBotAndpushOrShiftxm1 ctxxp1Eqxm1
      -- (stack(x) != ⊥ ∧ pop(x − 1)) → ctx(x + 1) = ctx(x - 1)
      popxm1 <- mkCheckPrec encData (zTake encData) xm1
      stackxNeqBotAndPopxm1 <- mkAnd [stackxNeqBot, popxm1]
      ctxxm1 <- mkApp1 (zCtx encData) xm1
      ctxxp1Eqctxx <- mkEq ctxxp1 ctxxm1
      popCtxRule <- mkImplies stackxNeqBotAndPopxm1 ctxxp1Eqctxx
      -- Final and
      mkAnd [ nextBackRules
            , smbRule, stackRule
            , botCtxRule, pushShiftCtxRule, popCtxRule
            ]

    -- SHIFT(x)
    mkShift :: EncData -> Word64 -> Z3 AST
    mkShift encData x = do
      let nodeSort = zNodeSort encData
          stack = zStack encData
          ctx = zCtx encData
      -- Propagate Next and Back operators
      nextBackRules <- mkNextBackRules encData x
      -- Bookkeeping functions
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      -- smb(x + 1) = struct(x)
      smbxp1 <- mkApp1 (zSmb encData) xp1
      structx <- mkApp1 (zStruct encData) xLit
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
      mkAnd [nextBackRules, smbRule, stackRule, ctxRule]

    -- POP(xExpr)
    mkPop :: EncData -> Word64 -> Z3 AST
    mkPop encData x = do
      let nodeSort = zNodeSort encData
          gamma = zGamma encData
          smb = zSmb encData
          stack = zStack encData
          ctx = zCtx encData
      xLit <- mkUnsignedInt64 x nodeSort
      xp1 <- mkUnsignedInt64 (x + 1) nodeSort
      stackx <- mkApp1 stack xLit
      -- ∀p((Γ(p, x) ∨ Γ((HNext Up p)_G, stack(x))) ↔ Γ(p, x + 1))
      let mkForallIff f = do
            let p = zFConstMap encData M.! f
            gammapx <- mkApp gamma [p, xLit]
            gammapxp1 <- mkApp gamma [p, xp1]
            mkIff gammapx gammapxp1
      gammaRule <- mkAndWith mkForallIff clos
      -- smb(x + 1) = smb(stack(x))
      smbxp1 <- mkApp1 smb xp1
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


encodeProg :: EncData -> Sort -> Map (Formula MP.ExprProp) AST
           -> FuncDecl -> FuncDecl -> FuncDecl
           -> FuncDecl -> FuncDecl -> FuncDecl
           -> MP.Program -> Word64 -> Z3 ()
encodeProg encData nodeSort fConstMap gamma struct yield equal take stack prog k = do
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
        checkPushx <- mkCheckPrec encData yield xLit
        pushProgx <- mkInput sVarFunVec locSort pc (MP.lsDPush lowerState) x
        pushxImpliesPushProgx <- mkImplies checkPushx pushProgx
        -- shift(x) → SHIFT(x)
        checkShiftx <- mkCheckPrec encData equal xLit
        shiftProgx <- mkInput sVarFunVec locSort pc (MP.lsDShift lowerState) x
        shiftxImpliesShiftProgx <- mkImplies checkShiftx shiftProgx
        -- pop(x) → POP(x)
        checkPopx <- mkCheckPrec encData take xLit
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
mkCheckPrec :: EncData -> FuncDecl -> AST -> Z3 AST
mkCheckPrec encData precRel x = do
  smbX <- mkApp1 (zSmb encData) x
  structX <- mkApp1 (zStruct encData) x
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

enableIf :: Bool -> Z3 AST -> Z3 AST
enableIf False _ = mkTrue
enableIf True m = m

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
        HNext _ g        -> f : closList g
        HBack _ _        -> error "Past operators not supported yet."
        WHNext _ g       -> f : closList g
        Until dir g h    -> [f, PNext dir f, XNext dir f] ++ closList g ++ closList h
        Release dir g h  -> [f, WPNext dir f, WXNext dir f] ++ closList g ++ closList h
        Since _ _ _      -> error "Past operators not supported yet."
        HUntil dir g h   -> [f, HNext dir f, HUntil dir T T] ++ closList g ++ closList h
        HRelease dir g h -> [f, WHNext dir f, HUntil dir T T] ++ closList g ++ closList h
        HSince _ _ _     -> error "Past operators not supported yet."
        Next g           -> f : closList g
        WNext g          -> f : closList g
        Back g           -> f : closList g
        WBack g          -> f : closList g
        Eventually g     -> [f, Next f] ++ closList g
        Always g         -> [f, WNext f] ++ closList g
        Once g           -> [f, Back f] ++ closList g
        Historically g   -> [f, WBack f] ++ closList g
        AuxBack _ _      -> error "AuxBack not supported in SMT encoding."

xnf :: Formula MP.ExprProp -> Formula MP.ExprProp
xnf f = case f of
  T                -> f
  Atomic _         -> f
  Not T            -> f
  Not (Atomic _)   -> f
  Not _            -> error "Supplied formula is not in Positive Normal Form."
  Or g h           -> Or (xnf g) (xnf h)
  And g h          -> And (xnf g) (xnf h)
  Xor g h          -> Xor (xnf g) (xnf h)
  Implies g h      -> Implies (xnf g) (xnf h)
  Iff g h          -> Iff (xnf g) (xnf h)
  PNext _ _        -> f
  PBack _ _        -> error "Past operators not supported yet."
  WPNext _ _       -> f
  XNext _ _        -> f
  XBack _ _        -> error "Past operators not supported yet."
  WXNext _ _       -> f
  HNext _ _        -> f
  HBack _ _        -> error "Past operators not supported yet."
  WHNext _ _       -> f
  Until dir g h    -> xnf h `Or` (xnf g `And` (PNext dir f `Or` XNext dir f))
  Release dir g h  -> xnf h `And` (xnf g `Or` (WPNext dir f `And` WXNext dir f))
  Since _ _ _      -> error "Past operators not supported yet."
  HUntil dir g h   -> (HUntil dir T T `And` xnf h) `Or` (xnf g `And` (HNext dir f))
  HRelease dir g h -> (HUntil dir T T `Implies` xnf h) `And` (xnf g `Or` WHNext dir f)
  HSince _ _ _     -> error "Past operators not supported yet."
  Next _           -> f
  WNext _          -> f
  Back _           -> f
  WBack _          -> f
  Eventually g     -> xnf g `Or` Next f
  Always g         -> xnf g `And` WNext f
  Once g           -> xnf g `Or` Back f
  Historically g   -> xnf g `And` WBack f
  AuxBack _ _      -> error "AuxBack not supported in SMT encoding."


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
