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

-- Precedence function for the Stack Trace Language Version 1
stlPrecedenceV1 :: Set (Prop String) -> Set (Prop String) -> Prec
stlPrecedenceV1 s1 s2
  | isCallSet s1 = callPrec s2
  | isRetSet  s1 = retPrec  s2
  | isHanSet  s1 = hanPrec  s2
  | isThrSet  s1 = thrPrec  s2
  | otherwise = error "First set has invalid tokens"
  where unprop (Prop p) = p
        calls s = filter ("c" `isPrefixOf`) (map unprop . S.toList $ s)
        rets  s = filter ("r" `isPrefixOf`) (map unprop . S.toList $ s)
        hans  s = filter ("h" `isPrefixOf`) (map unprop . S.toList $ s)
        thrs  s = filter ("t" `isPrefixOf`) (map unprop . S.toList $ s)
        isCallSet = not . null . calls
        isRetSet  = not . null .  rets
        isHanSet  = not . null .  hans
        isThrSet  = not . null .  thrs
        callPrec s
          | S.null    s = Take
          | isCallSet s = Yield
          | isRetSet  s = Equal
          | isHanSet  s = Yield
          | isThrSet  s = Take
          | otherwise = error "Second set has invalid tokens"
        retPrec s
          | S.null    s = Take
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isThrSet  s = Take
          | otherwise = error "Second set has invalid tokens"
        hanPrec s
          | S.null    s = Take
          | isCallSet s = Yield
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isThrSet  s = Yield
          | otherwise = error "Second set has invalid tokens"
        thrPrec s
          | S.null    s = Take
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isThrSet  s = Take
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
  where unprop (Prop p) = p
        calls s = filter ("c" `isPrefixOf`) (map unprop . S.toList $ s)
        rets  s = filter ("r" `isPrefixOf`) (map unprop . S.toList $ s)
        hans  s = filter ("h" `isPrefixOf`) (map unprop . S.toList $ s)
        excs  s = filter ("e" `isPrefixOf`) (map unprop . S.toList $ s)
        isCallSet = not . null . calls
        isRetSet  = not . null .  rets
        isHanSet  = not . null .  hans
        isExcSet  = not . null .  excs
        callPrec s
          | S.null    s = Take
          | isCallSet s = Yield
          | isRetSet  s = Equal
          | isHanSet  s = Yield
          | isExcSet  s = Take
          | otherwise = error "Second set has invalid tokens"
        retPrec s
          | S.null    s = Take
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isExcSet  s = Take
          | otherwise = error "Second set has invalid tokens"
        hanPrec s
          | S.null    s = Take
          | isCallSet s = Yield
          | isRetSet  s = Take
          | isHanSet  s = Yield
          | isExcSet  s = Equal
          | otherwise = error "Second set has invalid tokens"
        excPrec s
          | S.null    s = Take
          | isCallSet s = Take
          | isRetSet  s = Take
          | isHanSet  s = Take
          | isExcSet  s = Take
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
