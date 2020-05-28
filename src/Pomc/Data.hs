{- |
   Module      : Pomc.Data
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Data ( decodeAtom
                 , encode
                 , generate
                 , EncodedSet
                 , FormulaSet
                 ) where

import Pomc.RPotl

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU

import Data.Bit.ThreadSafe (Bit)
import qualified Data.Bit.ThreadSafe as B

type EncodedSet = Vector Bit
type FormulaSet a = Set (Formula a)

decodeAtom :: Ord a => (Int -> Formula a) -> EncodedSet -> FormulaSet a
decodeAtom fetch bv = let pos = map fetch (B.listBits bv)
                          neg = map (Not . fetch) (B.listBits . B.invertBits $ bv)
                      in S.fromList pos `S.union` S.fromList neg

encode :: (Formula a -> Int) -> Int -> FormulaSet a -> EncodedSet
encode lookup len set = let zeroes = VU.replicate len (B.Bit False)
                            pairs = S.toList $ S.map (\phi -> (lookup phi, B.Bit True)) set
                        in zeroes VU.// pairs

generate :: Int -> [Vector Bit]
generate len = VU.replicateM len [B.Bit False, B.Bit True]
