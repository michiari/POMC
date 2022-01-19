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

type Parser = Parsec Void Text

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

identifierP :: Parser Text
identifierP = (label "identifier") . L.lexeme spaceP $ do
  first <- choice [letterChar, char '_']
  rest <- many $ choice [alphaNumChar, char '_', char '.', char ':', char '=', char '~']
  return $ T.pack (first:rest)

boolLiteralP :: Parser IntValue
boolLiteralP = (BV.fromBool True <$ symbolP "true") <|> (BV.fromBool False <$ symbolP "false")

literalP :: Parser IntValue
literalP = boolLiteralP <|> unsignedLiteralP
  where unsignedLiteralP = try $ L.lexeme spaceP $ do
          value <- L.decimal :: Parser Integer
          _ <- char 'u'
          width <- L.decimal :: Parser Int
          return $ BV.bitVec width value

variableLookup :: Map Text Variable -> Text -> Parser Variable
variableLookup varmap vname = case M.lookup vname varmap of
                                Just var -> return var
                                Nothing  -> fail $ "Undeclared identifier: " ++ show vname

exprP :: Map Text Variable -> Parser Expr
exprP varmap = makeExprParser termP opTable
  where termP :: Parser Expr
        termP = choice
          [ fmap Literal literalP
          , fmap Term $ identifierP >>= variableLookup varmap
          , between (symbolP "(") (symbolP ")") (exprP varmap)
          ]

        opTable = [ [ Prefix (Not <$ symbolP "!") ]
                  , [ InfixL (Div <$ symbolP "/")
                    , InfixL (Rem <$ symbolP "%")
                    ]
                  , [ InfixL (Mul <$ symbolP "*") ]
                  , [ InfixL (Add <$ symbolP "+")
                    , InfixL (Sub <$ symbolP "-")
                    ]
                  , [ InfixL (Eq  <$ symbolP "==") -- TODO: add more comparisons
                    , InfixL (Leq <$ (try $ symbolP "<="))
                    , InfixL (Lt  <$ (try $ symbolP "<"))
                    ]
                  , [ InfixL (And <$ symbolP "&&") ]
                  , [ InfixL (Or  <$ symbolP "||") ]
                  ]

typeP :: Parser Int
typeP = (label "identifier") . L.lexeme spaceP $
        choice [ (1 <$ symbolP "bool")
               , char 'u' *> L.decimal
               ]

declP :: Parser [Variable]
declP = try $ do
  width <- typeP
  ids <- sepBy1 identifierP (symbolP ",")
  _ <- symbolP ";"
  return $ map (\name -> Variable width name) ids

declsP :: Parser (Set Variable)
declsP = (S.fromList . concat) <$> many declP

assP :: Map Text Variable -> Parser Statement
assP varmap = try $ do
  lhs <- identifierP
  _ <- symbolP "="
  rhs <- exprP varmap
  _ <- symbolP ";"
  var <- variableLookup varmap lhs
  return $ Assignment var rhs

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
stmtP varmap = choice [ assP varmap
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
  return $ FunctionSkeleton fname (parseModules fname) stmts

programP :: Parser Program
programP = do
  spaceP
  declSet <- declsP
  let varmap = M.fromList $ map (\var -> (varName var, var)) (S.toAscList declSet)
  sks <- some $ functionP varmap
  eof
  let p = Program declSet sks
      undeclFuns = undeclaredFuns p
  if S.null undeclFuns
    then return p
    else fail $ "Undeclared identifier(s): " ++
         show (S.toList undeclFuns)

undeclaredVars :: Program -> Set Variable
undeclaredVars p = S.difference actualVars (pVars p)
  where gatherExprVars :: Expr -> Set Variable
        gatherExprVars (Literal _) = S.empty
        gatherExprVars (Term v) = S.singleton v
        gatherExprVars (Not bexpr) = gatherExprVars bexpr
        gatherExprVars (And lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Or lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Add lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Sub lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Mul lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Div lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Rem lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Eq lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Lt lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs
        gatherExprVars (Leq lhs rhs) = gatherExprVars lhs `S.union` gatherExprVars rhs

        gatherVars :: Statement -> Set Variable
        gatherVars (Assignment v rhs) = S.insert v $ gatherExprVars rhs
        gatherVars (Call _) = S.empty
        gatherVars (TryCatch tryb catchb) = gatherBlockVars tryb `S.union` gatherBlockVars catchb
        gatherVars (IfThenElse (Just g) thenb elseb) =
          gatherExprVars g `S.union` gatherBlockVars thenb `S.union` gatherBlockVars elseb
        gatherVars (IfThenElse Nothing thenb elseb) =
          gatherBlockVars thenb `S.union` gatherBlockVars elseb
        gatherVars (While (Just g) body) = gatherExprVars g `S.union` gatherBlockVars body
        gatherVars (While Nothing body) = gatherBlockVars body
        gatherVars Throw = S.empty

        gatherBlockVars stmts =
          foldl (\gathered stmt -> gathered `S.union` gatherVars stmt) S.empty stmts

        actualVars =
          foldl (\gathered sk ->
                   gathered `S.union` (gatherBlockVars . skStmts $ sk)) S.empty (pSks p)

undeclaredFuns :: Program -> Set Text
undeclaredFuns p = S.difference usedFuns declaredFuns
  where declaredFuns = S.fromList $ map skName (pSks p)

        gatherFuns :: Statement -> Set Text
        gatherFuns (Assignment _ _) = S.empty
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
