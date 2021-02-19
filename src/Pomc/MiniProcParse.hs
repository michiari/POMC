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


type Parser = Parsec Void Text

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

identifierP :: Parser Text
identifierP = (label "identifier") . L.lexeme spaceP $ do
  first <- choice [letterChar, char '_']
  rest <- many $ choice [alphaNumChar, char '_', char '.']
  return $ T.pack (first:rest)

boolLiteralP :: Parser Bool
boolLiteralP = (True <$ symbolP "true") <|> (False <$ symbolP "false")

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
  rhs <- boolLiteralP
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
  guard <- ((Nothing <$ symbolP "*") <|> fmap Just identifierP)
  _ <- symbolP ")"
  thenBlock <- blockP
  _ <- symbolP "else"
  elseBlock <- blockP
  return $ IfThenElse guard thenBlock elseBlock

throwP :: Parser Statement
throwP = symbolP "throw" >> symbolP ";" >> return Throw

stmtP :: Parser Statement
stmtP = choice [ assP
               , callP
               , tryCatchP
               , iteP
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
      undeclVars = undeclared p
  if S.null undeclVars
    then return p
    else fail $ "Undeclared variable identifier(s): " ++ show (S.toList undeclVars)

undeclared :: Program -> Set Identifier
undeclared p = S.difference actualVars (pVars p)
  where gatherVars :: Statement -> Set Identifier
        gatherVars (Assignment v _) = S.singleton v
        gatherVars (TryCatch tryb catchb) = gatherBlockVars tryb `S.union` gatherBlockVars catchb
        gatherVars (IfThenElse (Just v) thenb elseb) =
          S.insert v (gatherBlockVars thenb `S.union` gatherBlockVars elseb)
        gatherVars (IfThenElse Nothing thenb elseb) =
          gatherBlockVars thenb `S.union` gatherBlockVars elseb
        gatherVars _ = S.empty

        gatherBlockVars stmts =
          foldl (\gathered stmt -> gathered `S.union` gatherVars stmt) S.empty stmts

        actualVars =
          foldl (\gathered sk ->
                   gathered `S.union` (gatherBlockVars . skStmts $ sk)) S.empty (pSks p)
