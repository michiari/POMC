{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.Parse
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Parse ( potlv2P
                  , checkRequestP
                  , spaceP
                  , CheckRequest(..)
                  , includeP
                  ) where

import Pomc.Prec (Prec(..), StructPrecRel, extractSLs, addEnd)
import Pomc.Prop (Prop(..))
import qualified Pomc.PotlV2 as P2
import Pomc.Example (stlPrecRelV2Text)
import Pomc.ModelChecker (ExplicitOpa(..), extractALs)

import Data.Void (Void)
import Data.Text
import Data.Set (Set)
import qualified Data.Set as S

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

type Parser = Parsec Void Text

type P2Formula = P2.Formula Text
type PropString = [Set (Prop Text)]

data CheckRequest = CheckRequest { creqPrecRels :: [StructPrecRel Text]
                                 , creqFormulas :: [P2Formula]
                                 , creqStrings  :: Maybe [PropString]
                                 , creqOpa :: Maybe (ExplicitOpa Word Text)
                                 }

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexemeP :: Parser a -> Parser a
lexemeP = L.lexeme spaceP

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

parensP :: Parser a -> Parser a
parensP = between (symbolP "(") (symbolP ")")

quotesP :: Parser a -> Parser a
quotesP = between (symbolP "\"") (symbolP "\"")

allPropChars :: Parser Char
allPropChars = choice [ alphaNumChar
                      , char ':', char '('
                      , char ')', char '&'
                      , char ' ', char '.'
                      , char '~', char '='
                      , char '-', char '+'
                      , char '<', char '>'
                      , char '_', char ';']

propP :: Parser (Prop Text)
propP = choice [ End         <$  symbolP "#"
               , Prop . pack <$> lexemeP (some alphaNumChar <?> "atomic proposition")
               , Prop . pack <$> quotesP (some allPropChars <?> "atomic proposition")
               ]

propSetP :: Parser (Set (Prop Text))
propSetP = choice [ S.singleton <$> propP
                  , S.fromList <$> parensP (some propP)
                  ]

propStringP :: Parser PropString
propStringP = some propSetP

precP :: Parser Prec
precP = choice [ Yield <$ symbolP "<"
               , Equal <$ symbolP "="
               , Take  <$ symbolP ">"
               ]

precRelP :: Parser (StructPrecRel Text)
precRelP = do sb1  <- propP
              prec <- precP
              sb2  <- propP
              return (sb1, sb2, prec)

potlv2P :: Parser P2Formula
potlv2P = makeExprParser termParser operatorTable
  where atomicP :: Parser P2Formula
        atomicP = P2.Atomic <$> propP

        trueP :: Parser P2Formula
        trueP = P2.T <$ symbolP "T"

        termParser :: Parser P2Formula
        termParser = choice
          [ trueP
          , atomicP
          , parensP potlv2P
          ]

        binaryL name f = InfixL (f <$ symbolP name)
        binaryR name f = InfixR (f <$ symbolP name)
        prefix name f = Prefix (f <$ symbolP name)

        operatorTable :: [[Operator Parser P2Formula]]
        operatorTable =
          [ [ prefix "Not" P2.Not
            , prefix "~"   P2.Not

            , prefix "PNd" (P2.PNext P2.Down)
            , prefix "PNu" (P2.PNext P2.Up)
            , prefix "PBd" (P2.PBack P2.Down)
            , prefix "PBu" (P2.PBack P2.Up)

            , prefix "XNd" (P2.XNext P2.Down)
            , prefix "XNu" (P2.XNext P2.Up)
            , prefix "XBd" (P2.XBack P2.Down)
            , prefix "XBu" (P2.XBack P2.Up)

            , prefix "HNd" (P2.HNext P2.Down)
            , prefix "HNu" (P2.HNext P2.Up)
            , prefix "HBd" (P2.HBack P2.Down)
            , prefix "HBu" (P2.HBack P2.Up)

            , prefix "Eventually" P2.Eventually
            , prefix "F"          P2.Eventually
            , prefix "Always" P2.Always
            , prefix "G"      P2.Always
            ]
          , [ binaryR "Ud" (P2.Until P2.Down)
            , binaryR "Uu" (P2.Until P2.Up)
            , binaryR "Sd" (P2.Since P2.Down)
            , binaryR "Su" (P2.Since P2.Up)

            , binaryR "HUd" (P2.HUntil P2.Down)
            , binaryR "HUu" (P2.HUntil P2.Up)
            , binaryR "HSd" (P2.HSince P2.Down)
            , binaryR "HSu" (P2.HSince P2.Up)
            ]
          , [ binaryL "And" P2.And
            , binaryL "&&"  P2.And
            ]
          , [ binaryL "Or" P2.Or
            , binaryL "||" P2.Or
            , binaryL "Xor" P2.Xor
            ]
          , [ binaryR "Implies" P2.Implies
            , binaryR "-->"     P2.Implies
            , binaryR "Iff"  P2.Iff
            , binaryR "<-->" P2.Iff
            ]
          ]

stateP :: Parser Word
stateP = L.lexeme spaceP L.decimal

stateListP :: Parser [Word]
stateListP = choice [ pure <$> stateP
                    , parensP (some stateP)
                    ]

deltaInputP :: Parser [(Word, Set (Prop Text), [Word])]
deltaInputP = parensP deltaRel `sepBy1` symbolP ","
  where deltaRel = do q <- stateP
                      _ <- symbolP ","
                      a <- propSetP
                      _ <- symbolP ","
                      ps <- stateListP
                      return (q, a, ps)

deltaPopP :: Parser [(Word, Word, [Word])]
deltaPopP = parensP deltaRel `sepBy1` symbolP ","
  where deltaRel = do q <- stateP
                      _ <- symbolP ","
                      s <- stateP
                      _ <- symbolP ","
                      ps <- stateListP
                      return (q, s, ps)

formulaSectionP :: Parser [P2Formula]
formulaSectionP = do _ <- symbolP "formulas"
                     _ <- symbolP "="
                     formulas <- formulasP
                     _ <- symbolP ";"
                     return formulas
  where formulasP = potlv2P `sepBy1` symbolP ","

stringSectionP :: Parser [PropString]
stringSectionP = do _ <- symbolP "strings"
                    _ <- symbolP "="
                    propStrings <- propStringsP
                    _ <- symbolP ";"
                    return propStrings
  where propStringsP = propStringP `sepBy1` symbolP ","

precSectionP :: Parser [StructPrecRel Text]
precSectionP = do _ <- symbolP "prec"
                  _ <- symbolP "="
                  precRels <- (stlPrecRelV2Text <$ symbolP "Mcall") <|> precRelsP
                  _ <- symbolP ";"
                  return precRels
  where precRelsP = precRelP `sepBy1` symbolP "," >>= return . addEnd

opaSectionP :: Parser (ExplicitOpa Word Text)
opaSectionP = do
  _ <- symbolP "opa"
  _ <- symbolP ":"
  _ <- symbolP "initials"
  _ <- symbolP "="
  opaInitials <- stateListP
  _ <- symbolP ";"
  _ <- symbolP "finals"
  _ <- symbolP "="
  opaFinals <- stateListP
  _ <- symbolP ";"
  _ <- symbolP "deltaPush"
  _ <- symbolP "="
  opaDeltaPush <- deltaInputP
  _ <- symbolP ";"
  _ <- symbolP "deltaShift"
  _ <- symbolP "="
  opaDeltaShift <- deltaInputP
  _ <- symbolP ";"
  _ <- symbolP "deltaPop"
  _ <- symbolP "="
  opaDeltaPop <- deltaPopP
  _ <- symbolP ";"
  return (ExplicitOpa ([], []) [] opaInitials opaFinals opaDeltaPush opaDeltaShift opaDeltaPop)

checkRequestP :: Parser CheckRequest
checkRequestP = do
  prs <- precSectionP
  fs  <- formulaSectionP
  pss <- optional stringSectionP
  opa <- optional opaSectionP
  return (CheckRequest prs fs pss (fullOpa opa prs))

fullOpa :: Maybe (ExplicitOpa Word Text)
        -> [StructPrecRel Text]
        -> Maybe (ExplicitOpa Word Text)
fullOpa Nothing _ = Nothing
fullOpa (Just opa) prs = Just $ ExplicitOpa
                         { sigma = (sls, als)
                         , precRel = prs
                         , initials = initials opa
                         , finals = finals opa
                         , deltaPush = deltaPush opa
                         , deltaShift = deltaShift opa
                         , deltaPop = deltaPop opa
                         }
  where sls = extractSLs prs  -- structural labels
        als = S.toList $
              (S.fromList (extractALs $ deltaPush opa)
               `S.union` S.fromList (extractALs $ deltaShift opa))
              `S.difference` (S.fromList sls) -- only normal labels, remove structural labels


includeP :: Parser String
includeP = do
  _ <- symbolP "include"
  _ <- symbolP "="
  path <- quotesP . some $ anySingleBut '"'
  _ <- symbolP ";"
  return path
