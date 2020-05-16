module POMC.Data ( decode
                 , generate
                 , EncodedSet
                 , FormulaSet
                 ) where

import POMC.RPotl

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU

import Data.Bit.ThreadSafe (Bit)
import qualified Data.Bit.ThreadSafe as B

type EncodedSet = Vector Bit
type FormulaSet a = Set (Formula a)

decode :: Ord a => (Int -> Formula a) -> EncodedSet -> FormulaSet a
decode fetch bv = let pos = map fetch (B.listBits bv)
                      neg = map (Not . fetch) (B.listBits . B.invertBits $ bv)
                  in S.fromList pos `S.union` S.fromList neg

generate :: Int -> [Vector Bit]
generate len = VU.replicateM len [B.Bit False, B.Bit True]
