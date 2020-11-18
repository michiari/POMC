{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.MiniProcParse
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProcParse ( programP ) where

import Pomc.OpaGen

import Data.Void (Void)
import Data.Text as T
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


type Parser = Parsec Void Text

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

identifierP :: Parser Text
identifierP = label "identifier" $ try $ L.lexeme spaceP $ do
  first <- letterChar
  rest <- some alphaNumChar
  return $ T.pack (first:rest)

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
  thenBlock <- blockP
  _ <- symbolP "else"
  elseBlock <- blockP
  return $ IfThenElse thenBlock elseBlock

throwP :: Parser Statement
throwP = symbolP "throw" >> symbolP ";" >> return Throw

stmtP :: Parser Statement
stmtP = choice [ callP
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

programP :: Parser [FunctionSkeleton]
programP = spaceP *> (some functionP) <* eof
