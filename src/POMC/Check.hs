module POMC.Check ( clos
                  , atoms
                  , consistent
                  , printAtoms
                  ) where

import POMC.Potl

import Data.Set (Set)
import qualified Data.Set as S

clos :: Ord a => Formula a -> [Prop a] -> Set (Formula a)
clos phi props = let propClos = concatMap (\p -> closList $ Atomic p) props
                     phiClos  = closList phi
                 in S.fromList (propClos ++ phiClos)
                 where
                   closList f = case f of
                     Atomic _        -> [f, Not f]
                     Not g           -> [f] ++ closList g
                     Or g h          -> [f, Not f] ++ closList g ++ closList h
                     And g h         -> [f, Not f] ++ closList g ++ closList h
                     PrecNext _ g    -> [f, Not f] ++ closList g
                     PrecBack _ g    -> [f, Not f] ++ closList g
                     ChainNext _ g   -> [f, Not f] ++ closList g
                     ChainBack _ g   -> [f, Not f] ++ closList g
                     Until _ g h     -> [f, Not f] ++ closList g ++ closList h
                     Since _ g h     -> [f, Not f] ++ closList g ++ closList h
                     HierNext _ g    -> [f, Not f] ++ closList g
                     HierBack _ g    -> [f, Not f] ++ closList g
                     HierUntil _ g h -> [f, Not f] ++ closList g ++ closList h
                     HierSince _ g h -> [f, Not f] ++ closList g ++ closList h

atoms :: Ord a => Set (Formula a) -> Set (Set (Formula a))
atoms = S.filter consistent . S.powerSet

consistent :: Ord a => Set (Formula a) -> Bool
consistent atom = negcons atom && andorcons atom
  where
    negcons atom   = True  `S.notMember` (S.map
                       (\f -> (negation f) `S.member` atom
                       ) atom)
    andorcons atom = False `S.notMember` (S.map
                       (\f -> case f of
                         And g h -> g `S.member` atom && h `S.member` atom
                         Or  g h -> g `S.member` atom || h `S.member` atom
                         _       -> True
                       ) atom)

printAtoms :: Show a => Set (Set (Formula a)) -> IO ()
printAtoms = putStr . unlines . (map (\at -> show (S.toList at))) . S.toList
