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

import Data.BitVector (BitVector)
import qualified Data.BitVector as BV

import Control.DeepSeq (NFData(..), rwhnf)
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


newtype BVEA = BVEA BitVector deriving (Eq, Ord, Show)

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
