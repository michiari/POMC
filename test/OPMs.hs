{- |
   Module      : Pomc.OPMs
   Copyright   : 2020 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module OPMs ( -- * Stack Trace Language V1 precedence function
              stlAnnotateV1
            , stlPrecRelV1
              -- * Stack Trace Language V2 precedence function
            , stlPrecRelV2
            , stlPrecV2sls
            ) where

import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.Prop (Prop(..))

import Data.List (isPrefixOf)


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
