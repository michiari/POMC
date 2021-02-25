module Pomc.PropConv (
                       APType
                     , convPropTokens
                     , convPropLabels
                     , convAP
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.PotlV2 (Formula, getProps)
import Pomc.Prec (StructPrecRel)

import Data.List (nub)
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Vector as V

-- an APType is basically a number
type APType = Word



convPropTokens :: (Ord a)
               => Formula a -- input formula phi
               -> [StructPrecRel a] --precedence relation which replaces the usual matrix M
               -> [Set (Prop a)] -- input tokens
               -> (Formula APType, [StructPrecRel APType], [Set (Prop APType)])
convPropTokens phi precr tokens =
  let tsAP = Set.toList $ foldl Set.union Set.empty tokens -- get a unique list of all input AP
      (tphi, tprec, trans, _) = convAP phi precr tsAP
      -- convert input tokens into set of APTypes: note that L(OPA) = Powerset(AP), so each input token is a set of AP
      ttokens = map (\t -> Set.map (\p -> fmap trans p) t) tokens -- for each set t, apply trans to each property stored in t
  in (tphi, tprec, ttokens)

-- convert generic props into APType props
convPropLabels :: (Ord a)
              => Formula a -- input formula phi
              -> ([Prop a], [Prop a]) -- the AP of the input alphabet (the first list is for structural labels, the second one is for normal labels)
              -> [StructPrecRel a] --precedence relation which replaces the usual matrix M
              -> (Formula APType, ([Prop APType], [Prop APType]), [StructPrecRel APType], APType -> a)
convPropLabels phi (sls, als) precr =
  let (tphi, tprec, trans, index) = convAP phi precr (sls ++ als)
  in (tphi, (map (fmap trans) sls, map (fmap trans) als), tprec, index)

-- convert generic props into APType props
convAP :: (Ord a)
       => Formula a -- input formula phi
       -> [StructPrecRel a] --precedence relation which replaces the usual matrix M
       -> [Prop a] -- input string
       -> (Formula APType, [StructPrecRel APType], a -> APType, APType -> a)
convAP phi precr other =
  let phiAP = getProps phi
      relAP = concatMap (\(sl1, sl2, _) -> [sl1, sl2]) precr
      -- nub removes duplicates
      allProps = map (\(Prop p) -> p) (filter (\p -> p /= End) $ nub $ other ++ phiAP ++ relAP)
      -- zip takes two lists and returns a list of corresponding pairs
      apMap = Map.fromList $ zip allProps [1..]
      -- given a prop expressed in a custom type(p), look for the corresponding number in the Map
      trans p = fromJust $ Map.lookup p apMap

      apVec = V.fromList $ allProps
      index i = apVec V.! ((fromIntegral i) - 1) -- index 0 is reserved for End
  in (fmap trans phi -- we need fmap because props are stored in the container Prop -> fmap:: Functor f --> (a -> b) -> f a 
     , map (\(sl1, sl2, pr) -> ( fmap trans $ sl1
                               , fmap trans $ sl2
                               , pr
                               )
           ) precr
     , trans
     , index
     )
