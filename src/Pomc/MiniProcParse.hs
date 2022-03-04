{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.MiniProcParse
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProcParse ( programP ) where

import Pomc.MiniProc

import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import qualified Data.BitVector as BV

data IdentifierIdInfo = IdentifierIdInfo { scalarIds :: IdType
                                         , arrayIds  :: IdType
                                         } deriving Show

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

composeSome :: (a -> Parser a) -> a -> Parser a
composeSome f arg = f arg >>= composeMany f

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
  where intLiteralP = try $ L.lexeme spaceP $ do
          value <- L.signed spaceP (L.lexeme spaceP L.decimal) :: Parser Integer
          ty <- intTypeP
          if value < 0 && not (isSigned ty)
            then fail "Negative literal declared unsigned"
            else return (BV.bitVec (typeWidth ty) value, ty)

variableP :: Map Text Variable -> Parser Variable
variableP varmap = identifierP >>= variableLookup
  where variableLookup :: Text -> Parser Variable
        variableLookup vname =
          case M.lookup vname varmap of
            Just var -> return var
            Nothing  -> fail $ "Undeclared identifier: " ++ show vname

arrayIndexP :: Map Text Variable -> Parser (Variable, TypedExpr)
arrayIndexP varmap = try $ do
  var <- variableP varmap
  _ <- symbolP "["
  idxExpr <- typedExprP varmap
  _ <- symbolP "]"
  return (var, idxExpr)

typedExprP :: Map Text Variable -> Parser TypedExpr
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
exprP varmap = untypeExpr <$> typedExprP varmap

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

declP :: (Map Text Variable, IdentifierIdInfo)
      -> Parser (Map Text Variable, IdentifierIdInfo)
declP (varmap, idIdInfo) = try $ do
  ty <- typeP
  names <- sepBy1 identifierP (symbolP ",")
  _ <- symbolP ";"
  let numIds = if isScalar ty then scalarIds idIdInfo else arrayIds idIdInfo
      numVars = fromIntegral $ length names :: IdType
      newVarMap = M.fromList
        $ map (\(name, vid) -> (name, Variable ty name vid))
        $ zip names [numIds + i | i <- [0..(numVars - 1)]]
  return ( varmap `M.union` newVarMap
         , if isScalar ty
           then idIdInfo { scalarIds = numIds + numVars }
           else idIdInfo { arrayIds = numIds + numVars }
         )

declsP :: (Map Text Variable, IdentifierIdInfo)
       -> Parser (Map Text Variable, IdentifierIdInfo)
declsP vmi = composeMany declP vmi

lValueP :: Map Text Variable -> Parser LValue
lValueP varmap = lArrayP <|> lScalarP
  where lScalarP = fmap LScalar $ variableP varmap
        lArrayP = fmap (\(var, idxExpr) -> LArray var $ untypeExpr idxExpr) $ arrayIndexP varmap

nondetP :: Map Text Variable -> Parser Statement
nondetP varmap = try $ do
  lhs <- lValueP varmap
  _ <- symbolP "="
  _ <- symbolP "*"
  _ <- symbolP ";"
  return $ Nondeterministic lhs

assP :: Map Text Variable -> Parser Statement
assP varmap = try $ do
  lhs <- lValueP varmap
  _ <- symbolP "="
  rhs <- typedExprP varmap
  _ <- symbolP ";"
  return $ Assignment lhs (untypeExprWithCast (lvalType lhs) rhs)
    where lvalType (LScalar var) = varType var
          lvalType (LArray var _) = scalarType . varType $ var

callP :: Parser Statement
callP = try $ do
  fname <- identifierP
  _ <- symbolP "()"
  _ <- symbolP ";"
  return $ Call fname

tryCatchP :: Map Text Variable -> Parser Statement
tryCatchP varmap = do
  _ <- symbolP "try"
  tryBlock <- blockP varmap
  _ <- symbolP "catch"
  catchBlock <- blockP varmap
  return $ TryCatch tryBlock catchBlock

iteP :: Map Text Variable -> Parser Statement
iteP varmap = do
  _ <- symbolP "if"
  _ <- symbolP "("
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just (exprP varmap))
  _ <- symbolP ")"
  thenBlock <- blockP varmap
  _ <- symbolP "else"
  elseBlock <- blockP varmap
  return $ IfThenElse guard thenBlock elseBlock

whileP :: Map Text Variable -> Parser Statement
whileP varmap = do
  _ <- symbolP "while"
  _ <- symbolP "("
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just (exprP varmap))
  _ <- symbolP ")"
  body <- blockP varmap
  return $ While guard body

throwP :: Parser Statement
throwP = symbolP "throw" >> symbolP ";" >> return Throw

stmtP :: Map Text Variable -> Parser Statement
stmtP varmap = choice [ nondetP varmap
                      , assP varmap
                      , callP
                      , tryCatchP varmap
                      , iteP varmap
                      , whileP varmap
                      , throwP
                      ] <?> "statement"

blockP :: Map Text Variable -> Parser [Statement]
blockP varmap = try $ do
  _ <- symbolP "{"
  stmts <- many (stmtP varmap)
  _ <- symbolP "}"
  return stmts

functionP :: Map Text Variable -> Parser FunctionSkeleton
functionP varmap = do
  fname <- identifierP
  _ <- symbolP "()"
  stmts <- blockP varmap
  return FunctionSkeleton { skName = fname
                          , skModules = (parseModules fname)
                          , skStmts = stmts
                          }

programP :: Parser Program
programP = do
  spaceP
  (varmap, _) <- declsP (M.empty, IdentifierIdInfo 0 0)
  sks <- some $ functionP varmap
  eof
  let (scalarVars, arrayVars) = S.partition (isScalar . varType) $ S.fromList $ M.elems varmap
      p = Program scalarVars arrayVars sks
      undeclFuns = undeclaredFuns p
  if S.null undeclFuns
    then return p
    else fail $ "Undeclared identifier(s): " ++
         show (S.toList undeclFuns)

undeclaredFuns :: Program -> Set Text
undeclaredFuns p = S.difference usedFuns declaredFuns
  where declaredFuns = S.fromList $ map skName (pSks p)

        gatherFuns :: Statement -> Set Text
        gatherFuns (Assignment _ _) = S.empty
        gatherFuns (Nondeterministic _) = S.empty
        gatherFuns (Call fname) = S.singleton fname
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
