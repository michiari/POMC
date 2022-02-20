{- |
   Module      : Pomc.Util
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.PropConv ( APType
                     , PropConv(..)
                     , makePropConv
                     , encodeFormula
                     , encodeStructPrecRel
                     , convProps
                     , convPropTokens
                     ) where

import Pomc.Prop (Prop(..), unprop, notEnd)
import Pomc.Potl (Formula, getProps)
import Pomc.Prec (StructPrecRel)

import Data.List (nub)
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Vector as V

-- internal representation of atomic propositions
type APType = Word

data PropConv a = PropConv { encodeAP :: a -> APType
                           , decodeAP :: APType -> a
                           , encodeProp :: Prop a -> Prop APType
                           , decodeProp :: Prop APType -> Prop a
                           }

makePropConv :: (Eq a, Ord a) => [Prop a] -> PropConv a
makePropConv props =
  let uniqueProps = map unprop $ filter notEnd $ nub props
      apMap = Map.fromList $ zip uniqueProps [1..]
      toAPType p = fromJust $ Map.lookup p apMap
      apVec = V.fromList $ uniqueProps
      fromAPType i = apVec V.! ((fromIntegral i) - 1) -- index 0 is reserved for End
  in PropConv { encodeAP = toAPType
              , decodeAP = fromAPType
              , encodeProp = fmap toAPType
              , decodeProp = fmap fromAPType
              }

encodeFormula :: PropConv a -> Formula a -> Formula APType
encodeFormula pconv phi = fmap (encodeAP pconv) phi

encodeStructPrecRel :: PropConv a -> [StructPrecRel a] -> [StructPrecRel APType]
encodeStructPrecRel pconv precr =
  map (\(sl1, sl2, pr) -> ( (encodeProp pconv) sl1
                          , (encodeProp pconv) sl2
                          , pr
                          )
      ) precr

-- convert generic props into APType props, and return a PropConv
convProps :: Ord a
          => Formula a -- input formula phi
          -> [StructPrecRel a] -- OPM
          -> [[Prop a]] -- APs outside phi and OPM
          -> ( Formula APType
             , [StructPrecRel APType]
             , [[Prop APType]]
             , PropConv a
             )
convProps phi precr others =
  let phiAP = getProps phi
      relAP = concatMap (\(sl1, sl2, _) -> [sl1, sl2]) precr
      pconv = makePropConv $ concat others ++ phiAP ++ relAP
  in ( encodeFormula pconv phi
     , encodeStructPrecRel pconv precr
     , map (map $ encodeProp pconv) others
     , pconv
     )

convPropTokens :: (Ord a)
               => Formula a -- input formula phi
               -> [StructPrecRel a] -- OPM
               -> [Set (Prop a)] -- input word
               -> ( Formula APType
                  , [StructPrecRel APType]
                  , [Set (Prop APType)]
                  )
convPropTokens phi precr tokens =
  let tsAP = Set.toList $ foldl Set.union Set.empty tokens -- get a list of all input APs
      (tphi, tprec, _, pconv) = convProps phi precr [tsAP] -- convert APs to APType
      ttokens = map (\t -> Set.map (encodeProp pconv) t) tokens -- convert input tokens to APType
  in (tphi, tprec, ttokens)
