{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.Parse.MiniProc
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Parse.MiniProc ( programP
                           , TypedExpr(..)
                           , TypedProp(..)
                           , untypeExprFormula
                           , identifierP
                           , typedExprP
                           ) where

import Pomc.MiniIR
import Pomc.Potl (Formula)

import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (isJust)
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad (foldM)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import qualified Data.BitVector as BV

type TypedValue = (IntValue, Type)
data TypedExpr = TLiteral TypedValue
               | TTerm Variable
               | TArrayAccess Variable TypedExpr
               -- Boolean operations
               | TNot TypedExpr
               | TAnd TypedExpr TypedExpr
               | TOr TypedExpr TypedExpr
               -- Arithmetic operations
               | TAdd TypedExpr TypedExpr
               | TSub TypedExpr TypedExpr
               | TMul TypedExpr TypedExpr
               | TDiv TypedExpr TypedExpr
               | TRem TypedExpr TypedExpr
               -- Comparisons
               | TEq TypedExpr TypedExpr
               | TLt TypedExpr TypedExpr
               | TLeq TypedExpr TypedExpr
               deriving Show

data TypedProp = TextTProp Text | ExprTProp (Maybe FunctionName) TypedExpr deriving Show

-- Convert a TypedExpr to an Expr by inserting appropriate casts
insertCasts :: TypedExpr -> (Expr, Type)
insertCasts (TLiteral (v, t)) = (Literal v, t)
insertCasts (TTerm v) = (Term v, varType v)
insertCasts (TArrayAccess v idxExpr) =
  (ArrayAccess v (fst $ insertCasts idxExpr), scalarType $ varType v)
-- All Boolean operators return a single bit
insertCasts (TNot te) = let (e0, _) = insertCasts te
                        in (Not e0, UInt 1)
insertCasts (TAnd te0 te1) = let (e0, _) = insertCasts te0
                                 (e1, _) = insertCasts te1
                             in (And e0 e1, UInt 1)
insertCasts (TOr te0 te1) = let (e0, _) = insertCasts te0
                                (e1, _) = insertCasts te1
                            in (Or e0 e1, UInt 1)
insertCasts (TAdd te0 te1) = evalBinOp Add Add te0 te1
insertCasts (TSub te0 te1) = evalBinOp Sub Sub te0 te1
insertCasts (TMul te0 te1) = evalBinOp Mul Mul te0 te1
insertCasts (TDiv te0 te1) = evalBinOp SDiv UDiv te0 te1
insertCasts (TRem te0 te1) = evalBinOp SRem URem te0 te1
insertCasts (TEq  te0 te1) = evalBinOp Eq Eq te0 te1
insertCasts (TLt  te0 te1) = evalBinOp SLt ULt te0 te1
insertCasts (TLeq te0 te1) = evalBinOp SLeq ULeq te0 te1

evalBinOp :: (Expr -> Expr -> a)
          -> (Expr -> Expr -> a)
          -> TypedExpr
          -> TypedExpr
          -> (a, Type)
evalBinOp sop uop te0 te1 = let (e0, t0) = insertCasts te0
                                (e1, t1) = insertCasts te1
                                t2 = commonType t0 t1
                                bop = if isSigned t2 then sop else uop
                            in (bop (addCast t0 t2 e0) (addCast t1 t2 e1), t2)

addCast :: Type -> Type -> Expr -> Expr
addCast ts td e | ws == wd = e
                | ws > wd = Trunc wd e
                | isSigned ts = SExt (wd - ws) e
                | otherwise = UExt (wd - ws) e
  where ws = typeWidth ts
        wd = typeWidth td

untypeExpr :: TypedExpr -> Expr
untypeExpr = fst . insertCasts

untypeExprWithCast :: Type -> TypedExpr -> Expr
untypeExprWithCast dt te = let (ex, st) = insertCasts te
                           in addCast st dt ex


type Parser = Parsec Void Text

composeMany :: (a -> Parser a) -> a -> Parser a
composeMany f arg = go arg
  where go arg0 = do
          r <- optional $ f arg0
          case r of
            Just arg1 -> go arg1
            Nothing -> return arg0

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

identifierP :: Parser Text
identifierP = (label "identifier") . L.lexeme spaceP $ do
  first <- choice [letterChar, char '_']
  rest <- many $ choice [alphaNumChar, char '_', char '.', char ':', char '=', char '~']
  return $ T.pack (first:rest)

boolLiteralP :: Parser TypedValue
boolLiteralP = ((BV.fromBool True, UInt 1) <$ symbolP "true")
               <|> ((BV.fromBool False, UInt 1) <$ symbolP "false")

literalP :: Parser TypedValue
literalP = boolLiteralP <|> intLiteralP
  where intLiteralP = L.lexeme spaceP $ do
          value <- L.signed spaceP (L.lexeme spaceP L.decimal) :: Parser Integer
          ty <- intTypeP
          if value < 0 && not (isSigned ty)
            then fail "Negative literal declared unsigned"
            else return (BV.bitVec (typeWidth ty) value, ty)

variableP :: Maybe (Map Text Variable) -> Parser Variable
variableP (Just varmap) = identifierP >>= variableLookup
  where variableLookup :: Text -> Parser Variable
        variableLookup vname =
          case M.lookup vname varmap of
            Just var -> return var
            Nothing  -> fail $ "Undeclared identifier: " ++ show vname
variableP Nothing = identifierP >>= -- Just return variable stub, to be replaced later
  (\vname -> return Variable { varType = UInt 0, varName = vname, varId = 0 })

arrayIndexP :: Maybe (Map Text Variable) -> Parser (Variable, TypedExpr)
arrayIndexP varmap = try $ do
  var <- variableP varmap
  _ <- symbolP "["
  idxExpr <- typedExprP varmap
  _ <- symbolP "]"
  return (var, idxExpr)

typedExprP :: Maybe (Map Text Variable) -> Parser TypedExpr
typedExprP varmap = makeExprParser termP opTable
  where termP :: Parser TypedExpr
        termP = choice
          [ fmap TLiteral literalP
          , fmap (\(var, idxExpr) -> TArrayAccess var idxExpr) $ arrayIndexP varmap
          , fmap TTerm $ variableP varmap
          , between (symbolP "(") (symbolP ")") (typedExprP varmap)
          ]

        opTable = [ [ Prefix (TNot <$ symbolP "!") ]
                  , [ InfixL (TDiv <$ symbolP "/")
                    , InfixL (TRem <$ symbolP "%")
                    ]
                  , [ InfixL (TMul <$ symbolP "*") ]
                  , [ InfixL (TAdd <$ symbolP "+")
                    , InfixL (TSub <$ symbolP "-")
                    ]
                  , [ InfixN (TEq       <$        symbolP "==")
                    , InfixN ((\x y -> TNot $ TEq x y) <$ symbolP "!=")
                    , InfixN (TLeq      <$ (try $ symbolP "<="))
                    , InfixN (TLt       <$ (try $ symbolP "<"))
                    , InfixN (flip TLeq <$ (try $ symbolP ">="))
                    , InfixN (flip TLt  <$ (try $ symbolP ">"))
                    ]
                  , [ InfixL (TAnd <$ symbolP "&&") ]
                  , [ InfixL (TOr  <$ symbolP "||") ]
                  ]

exprP :: Map Text Variable -> Parser Expr
exprP varmap = untypeExpr <$> typedExprP (Just varmap)

intTypeP :: Parser Type
intTypeP = fmap UInt (char 'u' *> L.decimal) <|> fmap SInt (char 's' *> L.decimal)

arrayTypeP :: Parser Type
arrayTypeP = try $ do
  elemType <- intTypeP
  _ <- symbolP "["
  size <- L.decimal
  _ <- symbolP "]"
  return $ case elemType of
             UInt w -> UIntArray w size
             SInt w -> SIntArray w size
             _      -> error "Arrays of arrays not supported."

typeP :: Parser Type
typeP = label "type" $ L.lexeme spaceP $
  choice [ (UInt 1 <$ (symbolP "bool" <|> symbolP "var"))
         , arrayTypeP
         , intTypeP
         ]

declP :: (Map Text Variable, VarIdInfo)
      -> Parser (Map Text Variable, VarIdInfo)
declP (varmap, vii) = try $ do
  ty <- typeP
  names <- sepBy1 identifierP (symbolP ",")
  _ <- symbolP ";"
  let numIds = if isScalar ty then scalarIds vii else arrayIds vii
      numVars = fromIntegral $ length names :: IdType
      newVarMap = M.fromList
        $ map (\(name, vid) -> (name, Variable ty name vid))
        $ zip names [numIds + i | i <- [0..(numVars - 1)]]
  return ( varmap `M.union` newVarMap
         , if isScalar ty
           then vii { scalarIds = numIds + numVars }
           else vii { arrayIds = numIds + numVars }
         )

declsP :: (Map Text Variable, VarIdInfo)
       -> Parser (Map Text Variable, VarIdInfo)
declsP vmi = composeMany declP vmi

lValueP :: Map Text Variable -> Parser LValue
lValueP varmap = lArrayP <|> lScalarP
  where lScalarP = fmap LScalar $ variableP $ Just varmap
        lArrayP = fmap (\(var, idxExpr) -> LArray var $ untypeExpr idxExpr)
                  $ arrayIndexP $ Just varmap

nondetP :: Map Text Variable -> Parser Statement
nondetP varmap = try $ do
  lhs <- lValueP varmap
  _ <- symbolP "="
  _ <- symbolP "*"
  _ <- symbolP ";"
  return $ Nondeterministic lhs

assOrCatP :: Map Text Variable -> Parser Statement
assOrCatP varmap = try $ do
  lhs <- lValueP varmap
  _ <- symbolP "="
  firstExpr <- teP
  maybeCat <- optional $ some ((,) <$> probP <*> teP)
  _ <- symbolP ";"
  let lhsType = case lhs of
        LScalar var -> varType var
        LArray var _ -> scalarType . varType $ var
  return $ case maybeCat of
    Nothing -> Assignment lhs (untypeExprWithCast lhsType firstExpr)
    Just l -> let (probs, exprs) = unzip l
              in Categorical lhs (map (untypeExprWithCast lhsType) (firstExpr:exprs)) probs
  where teP = typedExprP $ Just varmap
        probP = between (symbolP "{") (symbolP "}") L.float

callP :: Map Text Variable -> Parser (Statement, [[TypedExpr]])
callP varmap = try $ do
  fname <- identifierP
  _ <- symbolP "("
  aparams <- sepBy (typedExprP $ Just varmap) (symbolP ",")
  _ <- symbolP ")"
  _ <- symbolP ";"
  return (Call fname [], [aparams])

tryCatchP :: Map Text Variable -> Parser (Statement, [[TypedExpr]])
tryCatchP varmap = do
  _ <- symbolP "try"
  (tryBlock, tryAparams) <- blockP varmap
  _ <- symbolP "catch"
  (catchBlock, catchAparams) <- blockP varmap
  return (TryCatch tryBlock catchBlock, tryAparams ++ catchAparams)

iteP :: Map Text Variable -> Parser (Statement, [[TypedExpr]])
iteP varmap = do
  _ <- symbolP "if"
  _ <- symbolP "("
  guard <- (Nothing <$ symbolP "*") <|> (fmap Just (exprP varmap))
  _ <- symbolP ")"
  (thenBlock, thenAparams) <- blockP varmap
  _ <- symbolP "else"
  (elseBlock, elseAparams) <- blockP varmap
  return (IfThenElse guard thenBlock elseBlock, thenAparams ++ elseAparams)

whileP :: Map Text Variable -> Parser (Statement, [[TypedExpr]])
whileP varmap = do
  _ <- symbolP "while"
  _ <- symbolP "("
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just (exprP varmap))
  _ <- symbolP ")"
  (body, aparams) <- blockP varmap
  return (While guard body, aparams)

throwP :: Parser Statement
throwP = symbolP "throw" >> symbolP ";" >> return Throw

stmtP :: Map Text Variable -> Parser (Statement, [[TypedExpr]])
stmtP varmap = choice [ noParams $ nondetP varmap
                      , noParams $ assOrCatP varmap
                      , callP varmap
                      , tryCatchP varmap
                      , iteP varmap
                      , whileP varmap
                      , noParams $ throwP
                      ] <?> "statement"
  where noParams = fmap (\stmt -> (stmt, [[]]))

stmtsP :: Map Text Variable -> Parser ([Statement], [[TypedExpr]])
stmtsP varmap = do
  stmtAparams <- many (stmtP varmap)
  let stmts = map fst stmtAparams
      aparams = concat $ map snd stmtAparams
  return (stmts, aparams)

blockP :: Map Text Variable -> Parser ([Statement], [[TypedExpr]])
blockP varmap = try $ do
  _ <- symbolP "{"
  stmtsAparams <- stmtsP varmap
  _ <- symbolP "}"
  return stmtsAparams

fargsP :: VarIdInfo
       -> Parser (VarIdInfo, Map Text Variable, [FormalParam])
fargsP vii = do
  rawfargs <- sepBy fargP (symbolP ",")
  let (ridfargs, newVii) = foldl assignId ([], vii) rawfargs
      idfargs = reverse $ ridfargs
      varmap = M.fromList $ map (\(_, var) -> (varName var, var)) idfargs
      params = map (\(isvr, var) -> if isvr then ValueResult var else Value var) idfargs
  return (newVii, varmap, params)
  where assignId (accfargs, accvii) (isvr, var)
          | isScalar . varType $ var = ((isvr, var { varId = scalarIds accvii }):accfargs,
                                        accvii { scalarIds = scalarIds accvii + 1 })
          | otherwise                = ((isvr, var { varId = arrayIds accvii }):accfargs,
                                        accvii { arrayIds = arrayIds accvii + 1 })

        fargP :: Parser (Bool, Variable)
        fargP = do
          ty <- typeP
          isvr <- optional $ symbolP "&"
          name <- identifierP
          return (isJust isvr, Variable ty name 0)

functionP :: Map Text Variable
          -> VarIdInfo
          -> Parser (FunctionSkeleton, [[TypedExpr]])
functionP gvarmap vii = do
  fname <- identifierP
  _ <- symbolP "("
  (argvii, argvarmap, params) <- fargsP vii
  _ <- symbolP ")"
  _ <- symbolP "{"
  (dvarmap, _) <- declsP (M.empty, argvii)
  let lvarmap = argvarmap `M.union` dvarmap
  (stmts, aparams) <- stmtsP (lvarmap `M.union` gvarmap)
  _ <- symbolP "}"
  let (lScalars, lArrays) =
        S.partition (isScalar . varType) $ S.fromList $ M.elems lvarmap
  return ( FunctionSkeleton { skName = fname
                            , skModules = (parseModules fname)
                            , skParams = params
                            , skScalars = lScalars
                            , skArrays = lArrays
                            , skStmts = stmts
                            }
         , aparams
         )

programP :: Parser Program
programP = do
  spaceP
  (varmap, vii) <- declsP (M.empty, VarIdInfo 0 0)
  sksAparams <- some $ functionP varmap vii
  eof
  case matchParams sksAparams of
    Right sks ->
      let (scalarGlobs, arrayGlobs) = S.partition (isScalar . varType) $ S.fromList $ M.elems varmap
          (scalarLocs, arrayLocs) = foldl
            (\(sc, ar) sk -> (sc `S.union` skScalars sk, ar `S.union` skArrays sk))
            (S.empty, S.empty)
            sks
          p = Program scalarGlobs arrayGlobs scalarLocs arrayLocs sks
          undeclFuns = undeclaredFuns p
      in if S.null undeclFuns
      then return p
      else fail $ "Undeclared identifier(s): " ++ show (S.toList undeclFuns)
    Left ermsg -> fail ermsg

matchParams :: [(FunctionSkeleton, [[TypedExpr]])] -> Either String [FunctionSkeleton]
matchParams sksAparams = mapM skMatchParams sksAparams
  where skMap = M.fromList $ map (\(sk, _) -> (skName sk, sk)) sksAparams
        skMatchParams (sk, aparams) =
          (\(newStmts, _) -> sk { skStmts = newStmts }) <$> blockMatchParams (skStmts sk) aparams
        blockMatchParams stmts aparams =
          (\(rstmts, newAparams) -> (reverse rstmts, newAparams))
          <$> foldM stmtMatchParams ([], aparams) stmts
        stmtMatchParams (acc, aparams) stmt =
          (\(newStmt, newParams) -> (newStmt : acc, newParams)) <$> doMatchParam stmt aparams

        doMatchParam (Call fname _) (aparam:aparams)
          | length aparam == length calleeParams =
            (\newParams -> (Call fname newParams, aparams)) <$>
            mapM matchParam (zip aparam calleeParams)
          | otherwise = Left ("Function " ++ show (skName calleeSk) ++ " requires "
                              ++ show (length calleeParams) ++ " parameters, given: "
                              ++ show (length aparam))
          where calleeSk = skMap M.! fname
                calleeParams = skParams calleeSk
                matchParam (texpr, Value fvar)
                  | isScalar . varType $ fvar =
                    Right $ ActualVal $ untypeExprWithCast (varType fvar) texpr
                  | otherwise =
                      case texpr of
                        TTerm avar | varType avar == varType fvar -> Right $ ActualVal (Term avar)
                        _ -> Left "Type mismatch on array parameter."
                matchParam (TTerm avar, ValueResult fvar)
                  | varType avar == varType fvar = Right $ ActualValRes avar
                  | otherwise = Left "Type mismatch on array parameter."
                matchParam _ = Left "Value-result actual parameter must be variable names."
        doMatchParam (TryCatch tryb catchb) aparams = do
          (tryStmts, tryParams) <- blockMatchParams tryb aparams
          (catchStmts, catchParams) <- blockMatchParams catchb tryParams
          return (TryCatch tryStmts catchStmts, catchParams)
        doMatchParam (IfThenElse g thenb elseb) aparams = do
          (thenStmts, thenParams) <- blockMatchParams thenb aparams
          (elseStmts, elseParams) <- blockMatchParams elseb thenParams
          return (IfThenElse g thenStmts elseStmts, elseParams)
        doMatchParam (While g body) aparams = do
          (bodyStmts, bodyParams) <- blockMatchParams body aparams
          return (While g bodyStmts, bodyParams)
        doMatchParam stmt (_:aparams) = Right (stmt, aparams)
        doMatchParam _ _ = error "Statement list and params list are not isomorphic."

undeclaredFuns :: Program -> Set Text
undeclaredFuns p = S.difference usedFuns declaredFuns
  where declaredFuns = S.fromList $ map skName (pSks p)

        gatherFuns :: Statement -> Set Text
        gatherFuns (Assignment _ _) = S.empty
        gatherFuns (Nondeterministic _) = S.empty
        gatherFuns (Categorical {}) = S.empty
        gatherFuns (Call fname _) = S.singleton fname
        gatherFuns (TryCatch tryb catchb) = gatherBlockFuns tryb `S.union` gatherBlockFuns catchb
        gatherFuns (IfThenElse _ thenb elseb) = gatherBlockFuns thenb `S.union` gatherBlockFuns elseb
        gatherFuns (While _ body) = gatherBlockFuns body
        gatherFuns Throw = S.empty

        gatherBlockFuns stmts =
          foldl (\gathered stmt -> gathered `S.union` gatherFuns stmt) S.empty stmts

        usedFuns =
          foldl (\gathered sk ->
                   gathered `S.union` (gatherBlockFuns . skStmts $ sk)) S.empty (pSks p)

parseModules :: Text -> [Text]
parseModules fname = joinModules (head splitModules) (tail splitModules) []
  where sep = T.pack "::"
        splitModules = filter (not . T.null) $ T.splitOn sep fname
        joinModules _ [] acc = acc
        joinModules container [_] acc = container:acc
        joinModules container (m:ms) acc =
          let newModule = container `T.append` sep `T.append` m
          in joinModules newModule ms (container:acc)

untypeExprFormula :: Program -> Formula TypedProp -> Formula ExprProp
untypeExprFormula prog = fmap $ \p -> case p of
  -- Keep support for legacy feature of APs as variables without scope.
  -- Note: if local variables from different functions share the same name,
  -- will only recognize the one from the last function.
  TextTProp t | t `M.member` varScopeMap -> let (scope, v) = varScopeMap M.! t
                                            in ExprProp scope (Term v)
              | otherwise -> TextProp t
  ExprTProp scope texpr ->
    (ExprProp scope) . untypeExpr . resolveVars (makeEnv scope) $ texpr
  where
    toVarMap vf = M.fromList . map (\v -> (varName v, vf v)) . S.toList

    varScopeMap = M.fromList [(varName v, (Just $ skName sk, v))
                              | sk <- pSks prog, v <- S.toList $ skScalars sk]
                  `M.union` toVarMap (\v -> (Nothing, v)) (pGlobalScalars prog)

    gvarmap = toVarMap id (pGlobalScalars prog) `M.union` toVarMap id (pGlobalArrays prog)
    makeEnv (Just fname) = case find (\fsk -> skName fsk == fname) (pSks prog) of
      Just fsk -> toVarMap id (skScalars fsk)
                  `M.union` toVarMap id (skArrays fsk)
                  `M.union` gvarmap
      Nothing -> error $ "Undeclared function " ++ T.unpack fname
    makeEnv Nothing = gvarmap

    resolveVars varmap texpr = go texpr
      where go e = case e of
              tl@(TLiteral _) -> tl
              TTerm v      -> TTerm $ case varmap M.!? varName v of
                Just nv -> nv
                Nothing -> error $ "Undeclared variable " ++ T.unpack (varName v)
              TArrayAccess v idx -> TArrayAccess nvar $ go idx
                where nvar = case varmap M.!? varName v of
                        Just nv -> nv
                        Nothing -> error $ "Undeclared variable " ++ T.unpack (varName v)
              TNot te      -> TNot $ go te
              TAnd te1 te2 -> goBinOp TAnd te1 te2
              TOr te1 te2  -> goBinOp TOr te1 te2
              TAdd te1 te2 -> goBinOp TAdd te1 te2
              TSub te1 te2 -> goBinOp TSub te1 te2
              TMul te1 te2 -> goBinOp TMul te1 te2
              TDiv te1 te2 -> goBinOp TDiv te1 te2
              TRem te1 te2 -> goBinOp TRem te1 te2
              TEq te1 te2  -> goBinOp TEq te1 te2
              TLt te1 te2  -> goBinOp TLt te1 te2
              TLeq te1 te2 -> goBinOp TLeq te1 te2
            goBinOp op te1 te2 = op (go te1) (go te2)
