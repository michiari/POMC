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
                 , PropSet
                 , BitEncoding(..)
                 ) where

import Pomc.Prop (Prop)
import Pomc.RPotl
import Pomc.PropConv (APType)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Bits (Bits(..))

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
type PropSet = Set (Prop APType)

data BitEncoding = BitEncoding
  { fetch :: (Int -> Formula APType)
  , index :: (Formula APType -> Int)
  , width :: Int
  , propBits :: Int
  }

class EncodedAtom e where
  decode :: BitEncoding -> e -> FormulaSet
  pdecode :: BitEncoding -> e -> FormulaSet
  encode :: BitEncoding -> FormulaSet -> e
  generateFormulas :: BitEncoding -> [e]
  null :: e -> Bool
  member :: BitEncoding -> Formula APType -> e -> Bool
  any :: BitEncoding -> (Formula APType -> Bool) -> e -> Bool
  filter :: BitEncoding -> (Formula APType -> Bool) -> e -> e
  suchThat :: BitEncoding -> (Formula APType -> Bool) -> e
  intersect :: e -> e -> e
  union :: e -> e -> e

  joinInputFormulas :: e -> e -> e
  extractInput :: BitEncoding -> e -> e
  decodeInput :: BitEncoding -> e -> PropSet
  encodeInput :: BitEncoding -> PropSet -> e
  inputSuchThat :: BitEncoding -> (Prop APType -> Bool) -> e


newtype BVEA = BVEA BitVector deriving (Ord, Show)

instance Eq BVEA where
  (BVEA v1) == (BVEA v2) = v1 BV.==. v2

instance NFData BVEA where rnf = rwhnf

instance Hashable BVEA where
  hashWithSalt salt (BVEA bv) = {-# SCC "hashBVEA" #-} (hashWithSalt salt $ BV.nat bv)

instance EncodedAtom BVEA where
  decode bitenc (BVEA bv) =
    let pos = map (fetch bitenc) (listBits bv)
        neg = map (Not . (fetch bitenc)) (listBits . BV.complement $ bv)
    in S.fromList pos `S.union` S.fromList neg

  pdecode bitenc (BVEA bv) =
    S.fromList $ map (fetch bitenc) (listBits bv)
  {-# INLINABLE pdecode #-}

  encode bitenc set =
    BVEA $ S.foldl BV.setBit (BV.zeros $ width bitenc) (S.map (index bitenc) set)
  {-# INLINABLE encode #-}

  generateFormulas bitenc =
    let len = width bitenc - propBits bitenc
    in if len == 0
       then []
       else map (BVEA . BV.reverse) $ BV.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
  {-# INLINABLE generateFormulas #-}

  null (BVEA bv) = bv == BV.nil
  {-# INLINABLE null #-}

  member bitenc phi (BVEA bv) | negative phi = not $ bv BV.@. (index bitenc $ negation phi)
                              | otherwise = bv BV.@. (index bitenc $ phi)
  {-# INLINABLE member #-}

  any bitenc predicate (BVEA bv) = Prelude.any (predicate . (fetch bitenc)) $ listBits bv
  {-# INLINABLE any #-}

  filter bitenc predicate (BVEA bv) = BVEA . snd $ BV.foldr filterVec (0, BV.zeros $ BV.width bv) bv
    where filterVec b (i, acc) = if b && predicate (fetch bitenc $ i)
                                 then (i+1, BV.setBit acc i)
                                 else (i+1, acc)
  {-# INLINABLE filter #-}

  suchThat bitenc predicate = BVEA $ BV.fromBits bitList
    where len = width bitenc
          bitList = map (predicate . (fetch bitenc)) [(len-1), (len-2)..0]
  {-# INLINABLE suchThat #-}

  intersect (BVEA v1) (BVEA v2) = BVEA $ v1 .&. v2
  {-# INLINABLE intersect #-}

  union (BVEA v1) (BVEA v2) = BVEA $ v1 .|. v2
  {-# INLINABLE union #-}

  joinInputFormulas (BVEA v1) (BVEA v2) = BVEA $ v2 BV.# v1
  {-# INLINABLE joinInputFormulas #-}

  extractInput bitenc (BVEA bv) = BVEA $ BV.least (propBits bitenc) bv
  {-# INLINABLE extractInput #-}

  decodeInput bitenc (BVEA bv) =
    S.fromList $ map (getProp . (fetch bitenc)) (listBits bv)
    where getProp (Atomic p) = p
  {-# INLINABLE decodeInput #-}

  encodeInput bitenc set =
    BVEA $ S.foldl BV.setBit (BV.zeros $ propBits bitenc) (S.map (index bitenc . Atomic) set)
  {-# INLINABLE encodeInput #-}

  inputSuchThat bitenc predicate = BVEA $ BV.fromBits bitList
    where len = propBits bitenc
          bitList = map (atomicPred . (fetch bitenc)) [(len-1), (len-2)..0]
          atomicPred (Atomic p) = predicate p
  {-# INLINABLE inputSuchThat #-}


listBits :: BitVector -> [Int]
listBits v = snd $ BV.foldr (\b (i, l) -> if b then (i+1, i:l) else (i+1, l)) (0, []) v


newtype BitVecEA = BitVecEA (Vector Bit) deriving (Eq, Ord, Show, Generic, NFData)

instance Hashable Bit
instance Hashable BitVecEA where
  hashWithSalt salt (BitVecEA vb) =
    {-# SCC "hashBitVecEA:foldl" #-} (VU.foldl' (\acc v -> hashWithSalt acc v) salt ws)
    where ws = {-# SCC "hashBitVecEA:words" #-} B.cloneToWords vb

instance EncodedAtom BitVecEA where
  decode bitenc (BitVecEA bv) =
    let pos = map (fetch bitenc) (B.listBits bv)
        neg = map (Not . (fetch bitenc)) (B.listBits . B.invertBits $ bv)
    in S.fromList pos `S.union` S.fromList neg

  pdecode bitenc (BitVecEA bv) =
    S.fromList $ map (fetch bitenc) (B.listBits bv)

  encode bitenc set =
    let zeroes = VU.replicate (width bitenc) (B.Bit False)
        pairs = S.toList $ S.map (\phi -> (index bitenc $ phi, B.Bit True)) set
    in BitVecEA $ zeroes VU.// pairs

  generateFormulas bitenc = map BitVecEA $ VU.replicateM len [B.Bit False, B.Bit True]
    where len = width bitenc - propBits bitenc

  null (BitVecEA bv) = bv == (zeroBits :: Vector Bit)

  member bitenc phi (BitVecEA bv) | negative phi = not $ testBit bv (index bitenc $ negation phi)
                                  | otherwise = testBit bv (index bitenc $ phi)

  any bitenc predicate (BitVecEA bv) = Prelude.any (predicate . (fetch bitenc)) $ B.listBits bv

  filter bitenc predicate (BitVecEA bv) =
    let zeroes = VU.replicate (VU.length bv) (B.Bit False)
    in BitVecEA $ zeroes VU.// map (\i -> (i, B.Bit (predicate . (fetch bitenc) $ i))) (B.listBits bv)

  suchThat bitenc predicate =
    BitVecEA $ zeroes VU.// map (\i -> (i, B.Bit (predicate . (fetch bitenc) $ i))) [0..(len-1)]
    where len = width bitenc
          zeroes = VU.replicate len (B.Bit False)

  intersect (BitVecEA v1) (BitVecEA v2) = BitVecEA $ v1 .&. v2

  union (BitVecEA v1) (BitVecEA v2) = BitVecEA $ v1 .|. v2

  joinInputFormulas (BitVecEA v1) (BitVecEA v2) = BitVecEA $ v1 VU.++ v2

  extractInput bitenc (BitVecEA bv) = BitVecEA $ VU.take (propBits bitenc) bv

  decodeInput bitenc (BitVecEA bv) =
    S.fromList $ map (getProp . (fetch bitenc)) (B.listBits bv)
    where getProp (Atomic p) = p

  encodeInput bitenc set =
    let zeroes = VU.replicate (propBits bitenc) (B.Bit False)
        pairs = S.toList $ S.map (\phi -> (index bitenc . Atomic $ phi, B.Bit True)) set
    in BitVecEA $ zeroes VU.// pairs

  inputSuchThat bitenc predicate =
    BitVecEA $ zeroes VU.// map (\i -> (i, B.Bit (atomicPred . (fetch bitenc) $ i))) [0..(len-1)]
    where len = propBits bitenc
          zeroes = VU.replicate len (B.Bit False)
          atomicPred (Atomic p) = predicate p
