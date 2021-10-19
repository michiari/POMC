{-# LANGUAGE OverloadedStrings #-}

{- |
   Module      : Pomc.Parse
   Copyright   : 2020-2021 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Parse ( potlv2P
                  , checkRequestP
                  , spaceP
                  , CheckRequest(..)
                  , includeP
                  ) where

import Pomc.Prec (Prec(..), StructPrecRel, extractSLs, addEnd)
import Pomc.Prop (Prop(..))
import qualified Pomc.Potl as P
import Pomc.MiniProc (Program)
import Pomc.MiniProcParse (programP)
import Pomc.ModelChecker (ExplicitOpa(..), extractALs)

import Data.Void (Void)
import Data.Text
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, isJust, fromJust)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

type Parser = Parsec Void Text

type PFormula = P.Formula Text
type PropString = [Set (Prop Text)]

data CheckRequest = CheckRequest { creqPrecRels :: Maybe [StructPrecRel Text]
                                 , creqFormulas :: [PFormula]
                                 , creqStrings  :: Maybe [PropString]
                                 , creqOpa :: Maybe (ExplicitOpa Word Text)
                                 , creqMiniProc :: Maybe Program
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

potlv2P :: Parser PFormula
potlv2P = makeExprParser termParser operatorTable
  where atomicP :: Parser PFormula
        atomicP = P.Atomic <$> propP

        trueP :: Parser PFormula
        trueP = P.T <$ symbolP "T"

        termParser :: Parser PFormula
        termParser = choice
          [ trueP
          , atomicP
          , parensP potlv2P
          ]

        binaryL name f = InfixL (f <$ symbolP name)
        binaryR name f = InfixR (f <$ symbolP name)
        prefix name f = Prefix (f <$ symbolP name)

        operatorTable :: [[Operator Parser PFormula]]
        operatorTable =
          [ [ prefix "Not" P.Not
            , prefix "~"   P.Not

            , prefix "PNd" (P.PNext P.Down)
            , prefix "PNu" (P.PNext P.Up)
            , prefix "PBd" (P.PBack P.Down)
            , prefix "PBu" (P.PBack P.Up)

            , prefix "XNd" (P.XNext P.Down)
            , prefix "XNu" (P.XNext P.Up)
            , prefix "XBd" (P.XBack P.Down)
            , prefix "XBu" (P.XBack P.Up)

            , prefix "HNd" (P.HNext P.Down)
            , prefix "HNu" (P.HNext P.Up)
            , prefix "HBd" (P.HBack P.Down)
            , prefix "HBu" (P.HBack P.Up)

            , prefix "Eventually" P.Eventually
            , prefix "F"          P.Eventually
            , prefix "Always" P.Always
            , prefix "G"      P.Always
            ]
          , [ binaryR "Ud" (P.Until P.Down)
            , binaryR "Uu" (P.Until P.Up)
            , binaryR "Sd" (P.Since P.Down)
            , binaryR "Su" (P.Since P.Up)

            , binaryR "HUd" (P.HUntil P.Down)
            , binaryR "HUu" (P.HUntil P.Up)
            , binaryR "HSd" (P.HSince P.Down)
            , binaryR "HSu" (P.HSince P.Up)
            ]
          , [ binaryL "And" P.And
            , binaryL "&&"  P.And
            ]
          , [ binaryL "Or" P.Or
            , binaryL "||" P.Or
            , binaryL "Xor" P.Xor
            ]
          , [ binaryR "Implies" P.Implies
            , binaryR "-->"     P.Implies
            , binaryR "Iff"  P.Iff
            , binaryR "<-->" P.Iff
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

formulaSectionP :: Parser [PFormula]
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
                  precRels <- precRelsP
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

progSectionP :: Parser Program
progSectionP = do
  _ <- symbolP "program"
  _ <- symbolP ":"
  programP

checkRequestP :: Parser CheckRequest
checkRequestP = do
  fs  <- formulaSectionP
  prs <- optional precSectionP
  pss <- optional stringSectionP
  opa <- optional opaSectionP
  prog <- optional progSectionP
  if isNothing prs && (isJust pss || isJust opa)
    then fail "If a string or an OPA is supplied, an OPM must also be specified."
    else return (CheckRequest prs fs pss (fullOpa opa (fromJust prs)) prog)

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
              (S.fromList (extractALs $ deltaPush opa) -- all the labels defined by the push relation
               `S.union` S.fromList (extractALs $ deltaShift opa)) -- all the labels defined by the shift relation
              `S.difference` (S.fromList sls) -- only normal labels, remove structural labels


includeP :: Parser String
includeP = do
  _ <- symbolP "include"
  _ <- symbolP "="
  path <- quotesP . some $ anySingleBut '"'
  _ <- symbolP ";"
  return path
