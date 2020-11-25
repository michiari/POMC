{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Data
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Data ( EncodedSet
                 , FormulaSet
                 , PropSet
                 , BitEncoding(..)
                 , newBitEncoding
                 , decode
                 , pdecode
                 , encode
                 , singleton
                 , empty
                 , generateFormulas
                 , Pomc.Data.null
                 , member
                 , Pomc.Data.any
                 , Pomc.Data.filter
                 , suchThat
                 , intersect
                 , union
                 , joinInputFormulas
                 , extractInput
                 , decodeInput
                 , encodeInput
                 , inputSuchThat
                 ) where

import Pomc.Prop (Prop)
import Pomc.PotlV2
import Pomc.PropConv (APType)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Bits (Bits(..))

import Data.BitVector (BitVector)
import qualified Data.BitVector as BV

import Data.Hashable


type EncodedSet = EncodedAtom
type FormulaSet = Set (Formula APType)
type PropSet = Set (Prop APType)

-- a BitEncoding is just the "guide" to translate from a FormulaSet to a BitVector and viceversa
data BitEncoding = BitEncoding
  { fetch :: (Int -> Formula APType)
  , index :: (Formula APType -> Int)
  , width :: Int
  , propBits :: Int
  , maskProps :: EncodedAtom
  }

newBitEncoding :: (Int -> Formula APType)
               -> (Formula APType -> Int)
               -> Int
               -> Int
               -> BitEncoding
newBitEncoding fetch_ index_ width_ propBits_ =
  BitEncoding fetch_ index_ width_ propBits_ maskProps_
  --the vector is just a mask of ones of size propBits
  where maskProps_ = EncodedAtom $ BV.ones propBits_

--an encoded atom is just a BitVector
newtype EncodedAtom = EncodedAtom BitVector deriving (Eq, Ord, Show)

instance Hashable EncodedAtom where
  -- hash with salt the value represented by the bit vector
  hashWithSalt salt (EncodedAtom bv) = hashWithSalt salt $ BV.nat bv

---decode a BitVector into a formulaSet
decode :: BitEncoding -> EncodedAtom -> FormulaSet
decode bitenc (EncodedAtom bv) =
  let pos = map (fetch bitenc) (listBits bv) --all the positive formulas, according to the bitencoding
      neg = map (Not . (fetch bitenc)) (listBits . BV.complement $ bv) -- all the negative formulas, according to the bitencoding
  in S.fromList pos `S.union` S.fromList neg

--decode a BitVector into a formulaSet, keeping only positive formulas
pdecode :: BitEncoding -> EncodedAtom -> FormulaSet
pdecode bitenc (EncodedAtom bv) =
  S.fromList $ map (fetch bitenc) (listBits bv)
{-# INLINABLE pdecode #-}

--encode a set of formulas into a BitVector, given a BitEncoding which gives the order of formulas in the vector
encode :: BitEncoding -> FormulaSet -> EncodedAtom
encode bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ width bitenc) (S.map (index bitenc) set)
{-# INLINABLE encode #-}

--encode a single formula into a BitVector, given a BitEncoding which gives the order of formulas in the vector, and the size of the vector
singleton :: BitEncoding -> Formula APType -> EncodedAtom
singleton bitenc f =
  EncodedAtom $ BV.setBit (BV.zeros $ width bitenc) (index bitenc $ f)
{-# INLINABLE singleton #-}

--create an EncodedAtom of only zeros
empty :: BitEncoding -> EncodedAtom
empty bitenc = EncodedAtom . BV.zeros $ width bitenc
{-# INLINABLE empty #-}

-- generate a list of EncodedAtom where each atom has a different set of formulas
generateFormulas :: BitEncoding -> [EncodedAtom]
generateFormulas bitenc =
  let len = width bitenc - propBits bitenc
  in if len == 0
     then []
     else map (EncodedAtom . BV.reverse) $ BV.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
{-# INLINABLE generateFormulas #-}

--test whether the BitEncoding represents the zero number
null :: EncodedAtom -> Bool
null (EncodedAtom bv) = bv == BV.nil
{-# INLINE null #-}

--test whether a Formula is part of an EncodedAtom
-- foreach phi foreach EA (not phi belongs to EA <=> phi not belongs to EA)
-- @ operator is for indexing
member :: BitEncoding -> Formula APType -> EncodedAtom -> Bool
member bitenc phi (EncodedAtom bv) | negative phi = not $ bv BV.@. (index bitenc $ negation phi)
                            | otherwise = bv BV.@. (index bitenc $ phi)
{-# INLINABLE member #-}

--test whether any formula holding in EncodedAtom satisfies the predicate
any :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> Bool
any bitenc predicate (EncodedAtom bv) = Prelude.any (predicate . (fetch bitenc)) $ listBits bv
{-# INLINABLE any #-}

--filter the formulas of an EncodedAtom according to predicate
filter :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> EncodedAtom
filter bitenc predicate (EncodedAtom bv) = EncodedAtom . snd $ BV.foldr filterVec (0, BV.zeros $ BV.width bv) bv
  where filterVec b (i, acc) = if b && predicate (fetch bitenc $ i)
                               then (i+1, BV.setBit acc i)
                               else (i+1, acc)
{-# INLINABLE filter #-}

--get an EncodedAtom where all ones correspond to formulas which satisfy the predicate, and zeros to formulas which do not
suchThat :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom
suchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = width bitenc
        bitList = map (predicate . (fetch bitenc)) [(len-1), (len-2)..0]
{-# INLINABLE suchThat #-}

--bitwise AND between two BitVectors
intersect :: EncodedAtom -> EncodedAtom -> EncodedAtom
intersect (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .&. v2
{-# INLINE intersect #-}

--bitwise OR between two BitVectors
union :: EncodedAtom -> EncodedAtom -> EncodedAtom
union (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .|. v2
{-# INLINE union #-}

--concatenation of two BitVectors
joinInputFormulas :: EncodedAtom -> EncodedAtom -> EncodedAtom
joinInputFormulas (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v2 BV.# v1
{-# INLINABLE joinInputFormulas #-}

--INPUT = AP = finite set of atomic propositions
extractInput :: BitEncoding -> EncodedAtom -> EncodedAtom
extractInput bitenc ea = intersect ea (maskProps bitenc)
{-# INLINABLE extractInput #-}

--get the set of atomic proposition from an EncodedAtom
decodeInput :: BitEncoding -> EncodedAtom -> PropSet
decodeInput bitenc (EncodedAtom bv) =
  S.fromList $ map (getProp . (fetch bitenc)) (listBits bv)
  where getProp (Atomic p) = p
{-# INLINABLE decodeInput #-}

--encode a set of atomic Propositions into an EncodedAtom
encodeInput :: BitEncoding -> PropSet -> EncodedAtom
encodeInput bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ propBits bitenc) (S.map (index bitenc . Atomic) set)
{-# INLINABLE encodeInput #-}


--get an EncodedAtom where all ones correspond to atomic predicates which satisfy the predicate, and zeros to formulas which do not
--the same as suchThat, but we are discarding the formulas defined by BitEncoding
inputSuchThat :: BitEncoding -> (Prop APType -> Bool) -> EncodedAtom
inputSuchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = propBits bitenc
        bitList = map (atomicPred . (fetch bitenc)) [(len-1), (len-2)..0]
        atomicPred (Atomic p) = predicate p
{-# INLINABLE inputSuchThat #-}

--a list of all the positions in BitVector where there a one
listBits :: BitVector -> [Int]
listBits v = snd $ BV.foldr (\b (i, l) -> if b then (i+1, i:l) else (i+1, l)) (0, []) v
