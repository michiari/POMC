{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.MiniProcParse
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProcParse ( programP ) where

import Pomc.MiniProc

import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as S
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr


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

boolLiteralP :: Parser Bool
boolLiteralP = (True <$ symbolP "true") <|> (False <$ symbolP "false")

boolExprP :: Parser BoolExpr
boolExprP = makeExprParser termP opTable
  where termP :: Parser BoolExpr
        termP = choice
          [ fmap Literal boolLiteralP
          , fmap Term identifierP
          , between (symbolP "(") (symbolP ")") boolExprP
          ]

        opTable = [ [ Prefix (Not <$ symbolP "!") ]
                  , [ InfixL (Or  <$ symbolP "||") ]
                  , [ InfixL (And <$ symbolP "&&") ]
                  ]

declsP :: Parser (Set Identifier)
declsP = do
  _ <- symbolP "var"
  ids <- sepBy1 identifierP (symbolP ",")
  _ <- symbolP ";"
  return $ S.fromList ids

assP :: Parser Statement
assP = try $ do
  lhs <- identifierP
  _ <- symbolP "="
  rhs <- boolExprP
  _ <- symbolP ";"
  return $ Assignment lhs rhs

callP :: Parser Statement
callP = try $ do
  fname <- identifierP
  _ <- symbolP "()"
  _ <- symbolP ";"
  return $ Call fname

tryCatchP :: Parser Statement
tryCatchP = do
  _ <- symbolP "try"
  tryBlock <- blockP
  _ <- symbolP "catch"
  catchBlock <- blockP
  return $ TryCatch tryBlock catchBlock

iteP :: Parser Statement
iteP = do
  _ <- symbolP "if"
  _ <- symbolP "("
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just boolExprP)
  _ <- symbolP ")"
  thenBlock <- blockP
  _ <- symbolP "else"
  elseBlock <- blockP
  return $ IfThenElse guard thenBlock elseBlock

whileP :: Parser Statement
whileP = do
  _ <- symbolP "while"
  _ <- symbolP "("
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just boolExprP)
  _ <- symbolP ")"
  body <- blockP
  return $ While guard body

throwP :: Parser Statement
throwP = symbolP "throw" >> symbolP ";" >> return Throw

stmtP :: Parser Statement
stmtP = choice [ assP
               , callP
               , tryCatchP
               , iteP
               , whileP
               , throwP
               ] <?> "statement"

blockP :: Parser [Statement]
blockP = try $ do
  _ <- symbolP "{"
  stmts <- many stmtP
  _ <- symbolP "}"
  return stmts

functionP :: Parser FunctionSkeleton
functionP = do
  fname <- identifierP
  _ <- symbolP "()"
  stmts <- blockP
  return $ FunctionSkeleton fname stmts

programP :: Parser Program
programP = do
  spaceP
  decls <- optional . try $ declsP
  sks <- some functionP
  eof
  let declSet = case decls of
                  Just s -> s
                  Nothing -> S.empty
      p = Program declSet sks
      undeclVars = undeclaredVars p
      undeclFuns = undeclaredFuns p
  if S.null undeclVars && S.null undeclFuns
    then return p
    else fail $ "Undeclared identifier(s): " ++ show (S.toList undeclVars ++ S.toList undeclFuns)

undeclaredVars :: Program -> Set Identifier
undeclaredVars p = S.difference actualVars (pVars p)
  where gatherBExprVars :: BoolExpr -> Set Identifier
        gatherBExprVars (Literal _) = S.empty
        gatherBExprVars (Term v) = S.singleton v
        gatherBExprVars (Not bexpr) = gatherBExprVars bexpr
        gatherBExprVars (And lhs rhs) = gatherBExprVars lhs `S.union` gatherBExprVars rhs
        gatherBExprVars (Or lhs rhs) = gatherBExprVars lhs `S.union` gatherBExprVars rhs

        gatherVars :: Statement -> Set Identifier
        gatherVars (Assignment v rhs) = S.insert v $ gatherBExprVars rhs
        gatherVars (Call _) = S.empty
        gatherVars (TryCatch tryb catchb) = gatherBlockVars tryb `S.union` gatherBlockVars catchb
        gatherVars (IfThenElse (Just g) thenb elseb) =
          gatherBExprVars g `S.union` gatherBlockVars thenb `S.union` gatherBlockVars elseb
        gatherVars (IfThenElse Nothing thenb elseb) =
          gatherBlockVars thenb `S.union` gatherBlockVars elseb
        gatherVars (While (Just g) body) = gatherBExprVars g `S.union` gatherBlockVars body
        gatherVars (While Nothing body) = gatherBlockVars body
        gatherVars Throw = S.empty

        gatherBlockVars stmts =
          foldl (\gathered stmt -> gathered `S.union` gatherVars stmt) S.empty stmts

        actualVars =
          foldl (\gathered sk ->
                   gathered `S.union` (gatherBlockVars . skStmts $ sk)) S.empty (pSks p)

undeclaredFuns :: Program -> Set Identifier
undeclaredFuns p = S.difference usedFuns declaredFuns
  where declaredFuns = S.fromList $ map skName (pSks p)

        gatherFuns :: Statement -> Set Identifier
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
