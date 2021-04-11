{- |
   Module      : Pomc.Example
   Copyright   : 2020 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Example ( -- * Stack Trace Language V1 precedence function
                      stlPrecedenceV1
                    , stlAnnotateV1
                    , stlPrecRelV1
                      -- * Stack Trace Language V2 precedence function
                    , stlPrecedenceV2
                    , stlAnnotateV2
                    , stlPrecRelV2
                    , stlPrecV2sls
                    , stlPrecRelV2Text
                    , stlPrecV2slsText
                    ) where

import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.Prop (Prop(..))

import Data.List (isPrefixOf)
import qualified Data.Text as T
import Data.Maybe (fromMaybe)

import Data.Set (Set)
import qualified Data.Set as S


-- Precedence function for the Stack Trace Language Version 1
stlPrecedenceV1 :: Set (Prop String) -> Set (Prop String) -> Maybe Prec
stlPrecedenceV1 s1 s2
  | isCallSet s1 = callPrec s2
  | isRetSet  s1 = retPrec  s2
  | isHanSet  s1 = hanPrec  s2
  | isThrSet  s1 = thrPrec  s2
  | otherwise = Nothing
  where unprop (Prop p) = Just p
        unprop End      = Nothing
        isCallSet = any (fromMaybe False . fmap ("c" `isPrefixOf`) . unprop)
        isRetSet  = any (fromMaybe False . fmap ("r" `isPrefixOf`) . unprop)
        isHanSet  = any (fromMaybe False . fmap ("h" `isPrefixOf`) . unprop)
        isThrSet  = any (fromMaybe False . fmap ("t" `isPrefixOf`) . unprop)
        isEndSet = S.member End
        callPrec s
          | isCallSet s = Just Yield
          | isRetSet  s = Just Equal
          | isHanSet  s = Just Yield
          | isThrSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        retPrec s
          | isCallSet s = Just Take
          | isRetSet  s = Just Take
          | isHanSet  s = Just Yield
          | isThrSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        hanPrec s
          | isCallSet s = Just Yield
          | isRetSet  s = Just Take
          | isHanSet  s = Just Yield
          | isThrSet  s = Just Yield
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        thrPrec s
          | isCallSet s = Just Take
          | isRetSet  s = Just Take
          | isHanSet  s = Just Take
          | isThrSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing

-- Utility function to annotate Stack Trace Language Version 1 strings
-- Given a list of string tokens, if a token starts with 'c' it is annotated
-- with "call", if it starts with 'r' it is annoteted with "ret" and so on
stlAnnotateV1 :: [String] -> [[String]]
stlAnnotateV1 = map annotate
  where annotate t
          | t == "call" || t == "ret" || t == "han" || t == "thr" = [t]
          | "c" `isPrefixOf` t = [t, "call"]
          | "r" `isPrefixOf` t = [t,  "ret"]
          | "h" `isPrefixOf` t = [t,  "han"]
          | "t" `isPrefixOf` t = [t,  "thr"]
          | otherwise = error ("Invalid token: " ++ t)

-- Precedence function for the Stack Trace Language Version 2 (alias MCall)
stlPrecedenceV2 :: Set (Prop String) -> Set (Prop String) -> Maybe Prec
stlPrecedenceV2 s1 s2
  | isCallSet s1 = callPrec s2
  | isRetSet  s1 = retPrec  s2
  | isHanSet  s1 = hanPrec  s2
  | isExcSet  s1 = excPrec  s2
  | otherwise = Nothing
  where unprop (Prop p) = Just p
        unprop End      = Nothing
        isCallSet = any (fromMaybe False . fmap ("c" `isPrefixOf`) . unprop)
        isRetSet  = any (fromMaybe False . fmap ("r" `isPrefixOf`) . unprop)
        isHanSet  = any (fromMaybe False . fmap ("h" `isPrefixOf`) . unprop)
        isExcSet  = any (fromMaybe False . fmap ("e" `isPrefixOf`) . unprop)
        isEndSet = S.member End
        callPrec s
          | isCallSet s = Just Yield
          | isRetSet  s = Just Equal
          | isHanSet  s = Just Yield
          | isExcSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        retPrec s
          | isCallSet s = Just Take
          | isRetSet  s = Just Take
          | isHanSet  s = Just Take
          | isExcSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        hanPrec s
          | isCallSet s = Just Yield
          | isRetSet  s = Just Take
          | isHanSet  s = Just Yield
          | isExcSet  s = Just Equal
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing
        excPrec s
          | isCallSet s = Just Take
          | isRetSet  s = Just Take
          | isHanSet  s = Just Take
          | isExcSet  s = Just Take
          | isEndSet  s = Just Take
          | S.null    s = Just Take
          | otherwise = Nothing

-- Utility function to annotate Stack Trace Language Version 2 strings
-- Given a list of string tokens, if a token starts with 'c' it is annotated
-- with "call", if it starts with 'r' it is annoteted with "ret" and so on
stlAnnotateV2 :: [String] -> [[String]]
stlAnnotateV2 = map annotate
  where annotate t
          | t == "call" || t == "ret" || t == "han" || t == "exc" = [t]
          | "c" `isPrefixOf` t = [t, "call"]
          | "r" `isPrefixOf` t = [t,  "ret"]
          | "h" `isPrefixOf` t = [t,  "han"]
          | "e" `isPrefixOf` t = [t,  "exc"]
          | otherwise = error ("Invalid token: " ++ t)

stlPrecRelV1 :: [StructPrecRel String]
stlPrecRelV1 = map (\(sl1, sl2, pr) -> (Prop sl1, Prop sl2, pr)) precs
               ++ map (\p -> (Prop p, End, Take)) sl
  where precs = [ ("call", "call", Yield)
                , ("call", "ret",  Equal)
                , ("call", "han",  Yield)
                , ("call", "thr",  Take)
                , ("ret",  "call", Take)
                , ("ret",  "ret",  Take)
                , ("ret",  "han",  Yield)
                , ("ret",  "thr",  Take)
                , ("han",  "call", Yield)
                , ("han",  "ret",  Take)
                , ("han",  "han",  Yield)
                , ("han",  "thr",  Yield)
                , ("thr",  "call", Take)
                , ("thr",  "ret",  Take)
                , ("thr",  "han",  Take)
                , ("thr",  "thr",  Take)
                ]
        sl = ["call", "ret", "han", "thr"]

stlPrecRelV2 :: [StructPrecRel String]
stlPrecRelV2 = map (\(sl1, sl2, pr) -> (Prop sl1, Prop sl2, pr)) precs
               ++ map (\p -> (Prop p, End, Take)) sl
  where precs = [ ("call", "call", Yield)
                , ("call", "ret",  Equal)
                , ("call", "han",  Yield)
                , ("call", "exc",  Take)
                , ("ret",  "call", Take)
                , ("ret",  "ret",  Take)
                , ("ret",  "han",  Take)
                , ("ret",  "exc",  Take)
                , ("han",  "call", Yield)
                , ("han",  "ret",  Take)
                , ("han",  "han",  Yield)
                , ("han",  "exc",  Equal)
                , ("exc",  "call", Take)
                , ("exc",  "ret",  Take)
                , ("exc",  "han",  Take)
                , ("exc",  "exc",  Take)
                ]
        sl = ["call", "ret", "han", "exc"]

stlPrecV2sls :: [Prop String]
stlPrecV2sls = map Prop ["call", "ret", "exc", "han"]

stlPrecRelV2Text :: [StructPrecRel T.Text]
stlPrecRelV2Text = map (\(p1, p2, pr) -> (fmap T.pack p1, fmap T.pack p2, pr)) stlPrecRelV2

stlPrecV2slsText :: [Prop T.Text]
stlPrecV2slsText = map (fmap T.pack) stlPrecV2sls