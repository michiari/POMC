{-# LANGUAGE DeriveGeneric, DeriveAnyClass, FlexibleInstances #-}

{- |
   Module      : Pomc.Data
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Data ( EncodedAtom(..)
                 , EncodedSet
                 , FormulaSet
                 ) where

import Pomc.RPotl
import Pomc.PropConv (APType)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU

import Data.Bit (Bit)
import qualified Data.Bit as B

import Data.BitVector (BitVector)
import qualified Data.BitVector as BV

import Control.DeepSeq (NFData(..), rwhnf)
import GHC.Generics (Generic)
import Data.Hashable


type EncodedSet = BVEA
type FormulaSet = Set (Formula APType)


class EncodedAtom e where
  decode :: (Int -> Formula APType) -> e -> FormulaSet
  encode :: (Formula APType -> Int) -> Int -> FormulaSet -> e
  generate :: Int -> [e]
  (++) :: e -> e -> e


newtype BitVecEA = BitVecEA (Vector Bit) deriving (Eq, Ord, Show, Generic, NFData)

instance Hashable Bit
instance Hashable BitVecEA where
  hashWithSalt salt (BitVecEA vb) =
    {-# SCC "hashBitVecEA:foldl" #-} (VU.foldl' (\acc v -> hashWithSalt acc v) salt ws)
    where ws = {-# SCC "hashBitVecEA:words" #-} B.cloneToWords vb

instance EncodedAtom BitVecEA where
  decode fetch (BitVecEA bv) =
    let pos = map fetch (B.listBits bv)
        neg = map (Not . fetch) (B.listBits . B.invertBits $ bv)
    in S.fromList pos `S.union` S.fromList neg

  encode index len set =
    let zeroes = VU.replicate len (B.Bit False)
        pairs = S.toList $ S.map (\phi -> (index phi, B.Bit True)) set
    in BitVecEA $ zeroes VU.// pairs

  generate len = map BitVecEA $ VU.replicateM len [B.Bit False, B.Bit True]

  (BitVecEA v1) ++ (BitVecEA v2) = BitVecEA $ v1 VU.++ v2


newtype BVEA = BVEA BitVector deriving (Ord, Show)

instance Eq BVEA where
  (BVEA v1) == (BVEA v2) = v1 BV.==. v2

instance NFData BVEA where rnf = rwhnf

instance Hashable BVEA where
  hashWithSalt salt (BVEA bv) = {-# SCC "hashBVEA" #-} (hashWithSalt salt $ BV.nat bv)

instance EncodedAtom BVEA where
  decode fetch (BVEA bv) =
    let pos = map fetch (listBits bv)
        neg = map (Not . fetch) (listBits . BV.complement $ bv)
    in S.fromList pos `S.union` S.fromList neg
    where listBits v = snd $ BV.foldr (\b (i, l) -> if b then (i+1, i:l) else (i+1, l)) (0, []) v

  encode index len set =
    BVEA $ S.foldl BV.setBit (BV.zeros len) (S.map index set)

  generate 0 = []
  generate len = map (BVEA . BV.reverse) $ BV.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]

  (BVEA v1) ++ (BVEA v2) = BVEA $ v2 BV.# v1
