{- |
   Module      : Pomc.Util
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.PropConv ( APType
                     , convPropTokens
                     , convPropLabels
                     , convAP
                     ) where

import Pomc.Prop (Prop(..))
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

convPropTokens :: (Ord a)
               => Formula a -- input formula phi
               -> [StructPrecRel a] -- OPM
               -> [Set (Prop a)] -- input word
               -> (Formula APType, [StructPrecRel APType], [Set (Prop APType)])
convPropTokens phi precr tokens =
  let tsAP = Set.toList $ foldl Set.union Set.empty tokens -- get a list of all input APs
      (tphi, tprec, trans, _) = convAP phi precr tsAP -- convert APs to APType
      ttokens = map (\t -> Set.map (\p -> fmap trans p) t) tokens -- convert input tokens to APType
  in (tphi, tprec, ttokens)

-- convert generic props of a language into APType props
convPropLabels :: (Ord a)
              => Formula a -- input formula phi
              -> ([Prop a], [Prop a]) -- (structural labels, other APs)
              -> [StructPrecRel a] -- OPM
              -> (Formula APType, ([Prop APType], [Prop APType]), [StructPrecRel APType], APType -> a)
convPropLabels phi (sls, als) precr =
  let (tphi, tprec, trans, index) = convAP phi precr (sls ++ als)
  in (tphi, (map (fmap trans) sls, map (fmap trans) als), tprec, index)

-- convert generic props into APType props, and return a function which maps a generic prop into the correspondant APType
convAP :: (Ord a)
       => Formula a -- input formula phi
       -> [StructPrecRel a] -- OPM
       -> [Prop a] -- APs outside phi and OPM
       -> (Formula APType, [StructPrecRel APType], a -> APType, APType -> a)
convAP phi precr other =
  let phiAP = getProps phi
      relAP = concatMap (\(sl1, sl2, _) -> [sl1, sl2]) precr
      allProps = map (\(Prop p) -> p) (filter (\p -> p /= End) $ nub $ other ++ phiAP ++ relAP)
      apMap = Map.fromList $ zip allProps [1..]

      -- map APs to their APType value
      trans p = fromJust $ Map.lookup p apMap
      apVec = V.fromList $ allProps
      index i = apVec V.! ((fromIntegral i) - 1) -- index 0 is reserved for End
  in ( fmap trans phi
     , map (\(sl1, sl2, pr) -> ( fmap trans $ sl1
                               , fmap trans $ sl2
                               , pr
                               )
           ) precr
     , trans
     , index
     )
