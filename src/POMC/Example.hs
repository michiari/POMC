module POMC.Example ( stlPrecedenceV1
                    , stlAnnotateV1
                    , stlPrecedenceV2
                    , stlAnnotateV2
                    ) where

import POMC.Opa (Prec(..))
import POMC.RPotl (Prop(..))

import Data.List (isPrefixOf)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Maybe (fromJust, fromMaybe)

-- Precedence function for the Stack Trace Language Version 1
stlPrecedenceV1 :: Set (Prop String) -> Set (Prop String) -> Prec
stlPrecedenceV1 s1 s2
  | isCallSet s1 = callPrec s2
  | isRetSet  s1 = retPrec  s2
  | isHanSet  s1 = hanPrec  s2
  | isThrSet  s1 = thrPrec  s2
  | otherwise = error "First set has invalid tokens"
  where unprop (Prop p) = Just p
        unprop End      = Nothing
        isCallSet = any (fromMaybe False . fmap ("c" `isPrefixOf`) . unprop)
        isRetSet  = any (fromMaybe False . fmap ("r" `isPrefixOf`) . unprop)
        isHanSet  = any (fromMaybe False . fmap ("h" `isPrefixOf`) . unprop)
        isThrSet  = any (fromMaybe False . fmap ("t" `isPrefixOf`) . unprop)
        isEndSet = S.member End
        callPrec s
          | isCallSet s = Yield
          | isRetSet  s = Equal
          | isHanSet  s = Yield
          | isThrSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        retPrec s
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isThrSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        hanPrec s
          | isCallSet s = Yield
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isThrSet  s = Yield
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        thrPrec s
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isThrSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"

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

-- Precedence function for the Stack Trace Language Version 2
stlPrecedenceV2 :: Set (Prop String) -> Set (Prop String) -> Prec
stlPrecedenceV2 s1 s2
  | isCallSet s1 = callPrec s2
  | isRetSet  s1 = retPrec  s2
  | isHanSet  s1 = hanPrec  s2
  | isExcSet  s1 = excPrec  s2
  | otherwise = error "First set has invalid tokens"
  where unprop (Prop p) = Just p
        unprop End      = Nothing
        isCallSet = any (fromMaybe False . fmap ("c" `isPrefixOf`) . unprop)
        isRetSet  = any (fromMaybe False . fmap ("r" `isPrefixOf`) . unprop)
        isHanSet  = any (fromMaybe False . fmap ("h" `isPrefixOf`) . unprop)
        isExcSet  = any (fromMaybe False . fmap ("e" `isPrefixOf`) . unprop)
        isEndSet = S.member End
        callPrec s
          | isCallSet s = Yield
          | isRetSet  s = Equal
          | isHanSet  s = Yield
          | isExcSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        retPrec s
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isExcSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        hanPrec s
          | isCallSet s = Yield
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isExcSet  s = Equal
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"
        excPrec s
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isExcSet  s = Take
          | isEndSet  s = Take
          | S.null    s = Take
          | otherwise = error "Second set has invalid tokens"

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
