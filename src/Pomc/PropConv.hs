module Pomc.PropConv (
                       APType
                     , convPropTokens
                     , convPropLabels
                     , convAP
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.RPotl (Formula, getProps)
import Pomc.Prec (StructPrecRel)

import Data.List (nub)
import Data.Maybe (fromJust)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Map as Map

type APType = Word

convPropTokens :: (Ord a)
               => Formula a
               -> [StructPrecRel a]
               -> [Set (Prop a)]
               -> (Formula APType, [StructPrecRel APType], [Set (Prop APType)])
convPropTokens phi precr tokens =
  let tsAP = Set.toList $ foldl Set.union Set.empty tokens
      (tphi, tprec, trans) = convAP phi precr tsAP
      ttokens = map (\t -> Set.map (\p -> fmap trans p) t) tokens
  in (tphi, tprec, ttokens)

convPropLabels :: (Ord a)
              => Formula a
              -> ([Prop a], [Prop a])
              -> [StructPrecRel a]
              -> (Formula APType, ([Prop APType], [Prop APType]), [StructPrecRel APType])
convPropLabels phi (sls, als) precr =
  let (tphi, tprec, trans) = convAP phi precr (sls ++ als)
  in (tphi, (map (fmap trans) sls, map (fmap trans) als), tprec)

convAP :: (Ord a)
       => Formula a
       -> [StructPrecRel a]
       -> [Prop a]
       -> (Formula APType, [StructPrecRel APType], a -> APType)
convAP phi precr other =
  let phiAP = getProps phi
      relAP = concatMap (\(sl1, sl2, _) -> [sl1, sl2]) precr
      allProps = map (\(Prop p) -> p) (filter (\p -> p /= End) $ nub $ other ++ phiAP ++ relAP)
      apMap = Map.fromList $ zip allProps [1..]
      trans p = fromJust $ Map.lookup p apMap
  in (fmap trans phi
     , map (\(sl1, sl2, pr) -> ( fmap trans $ sl1
                               , fmap trans $ sl2
                               , pr
                               )
           ) precr
     , trans
     )
