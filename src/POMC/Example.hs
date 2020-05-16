module POMC.Example ( stlPrecedence
                    , stlAnnotate
                    ) where

import POMC.Opa (Prec(..))
import POMC.RPotl (Prop(..))

import Data.List (isPrefixOf)

import Data.Set (Set)
import qualified Data.Set as S

-- Precedence function for the Stack Trace Language
stlPrecedence :: Set (Prop String) -> Set (Prop String) -> Prec
stlPrecedence s1 s2
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

stlAnnotate :: [String] -> [[String]]
stlAnnotate = map annotate
  where annotate t
          | t == "call" || t == "ret" || t == "han" || t == "thr" = [t]
          | "c" `isPrefixOf` t = [t, "call"]
          | "r" `isPrefixOf` t = [t,  "ret"]
          | "h" `isPrefixOf` t = [t,  "han"]
          | "t" `isPrefixOf` t = [t,  "thr"]
          | otherwise = error ("Invalid token: " ++ t)
