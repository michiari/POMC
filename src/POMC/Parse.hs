{-# LANGUAGE OverloadedStrings #-}

module POMC.Parse ( potlv2P
                  , checkRequestP
                  , spaceP
                  , CheckRequest(..)
                  ) where

import POMC.Prec (Prec(..))
import POMC.Prop (Prop(..))
import qualified POMC.PotlV2 as P2

import Data.Void (Void)

import Data.Text (Text)
import Data.Text as T

import Data.Set (Set)
import qualified Data.Set as S

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

type Parser = Parsec Void Text

type PrecRelation = (Set (Prop Text), Set (Prop Text), Prec)
type P2Formula = P2.Formula Text
type PropString = [Set (Prop Text)]

data CheckRequest = CheckRequest { creqPrecRels :: [PrecRelation]
                                 , creqFormulas :: [P2Formula]
                                 , creqStrings  :: [PropString]
                                 }

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexemeP :: Parser a -> Parser a
lexemeP = L.lexeme spaceP

symbolP :: Text -> Parser Text
symbolP = L.symbol spaceP

parensP :: Parser a -> Parser a
parensP = between (symbolP "(") (symbolP ")")

propP :: Parser (Prop Text)
propP = choice [ End           <$  symbolP "#"
               , Prop . T.pack <$> lexemeP (some alphaNumChar <?> "atomic proposition")
               ]

propSetP :: Parser (Set (Prop Text))
propSetP = choice [ S.singleton <$> propP
                  ,  S.fromList <$> parensP (some propP)
                  ]

propStringP :: Parser PropString
propStringP = some propSetP

precP :: Parser Prec
precP = choice [ Yield <$ symbolP "<"
               , Equal <$ symbolP "="
               , Take  <$ symbolP ">"
               ]

precRelP :: Parser PrecRelation
precRelP = do sb1  <- matchP
              prec <- precP
              sb2  <- matchP
              return (sb1, sb2, prec)
  where matchP = choice [ S.empty <$ symbolP "*" -- S.empty is subset of any set
                        , propSetP
                        ]

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

formulaSectionP :: Parser [P2Formula]
formulaSectionP = do symbolP "formulas"
                     symbolP "="
                     formulas <- formulasP
                     symbolP ";"
                     return formulas
  where formulasP = potlv2P `sepBy1` symbolP ","

stringSectionP :: Parser [PropString]
stringSectionP = do symbolP "strings"
                    symbolP "="
                    propStrings <- propStringsP
                    symbolP ";"
                    return propStrings
  where propStringsP = propStringP `sepBy1` symbolP ","

precSectionP :: Parser [PrecRelation]
precSectionP = do symbolP "prec"
                  symbolP "="
                  precRels <- precRelsP
                  symbolP ";"
                  return precRels
  where precRelsP = precRelP `sepBy1` symbolP ","

checkRequestP :: Parser CheckRequest
checkRequestP = do prs <- precSectionP
                   fs  <- formulaSectionP
                   pss <- stringSectionP
                   return (CheckRequest prs fs pss)
