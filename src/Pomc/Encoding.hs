{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Encoding
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}
module Pomc.Encoding ( EncodedSet
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
                     , powerSet
                     , Pomc.Encoding.null
                     , Pomc.Encoding.all
                     , member
                     , Pomc.Encoding.any
                     , Pomc.Encoding.filter
                     , suchThat
                     , intersect
                     , union
                     , joinInputFormulas
                     , extractInput
                     , sliceInput
                     , decodeInput
                     , encodeInput
                     , inputSuchThat
                     , generateInputs
                     , singletonInput
                     , Pomc.Encoding.nat
                     ) where

import Pomc.Potl
import Pomc.PropConv (APType)

import Data.Set (Set)
import qualified Data.Set as S
import Data.Bits (Bits(..))
import Data.BitVector (BitVector)
import qualified Data.BitVector as BV
import Data.Hashable
import Control.Monad (foldM)

type EncodedSet = EncodedAtom
type FormulaSet = Set (Formula APType)
type PropSet = Set (Prop APType)

-- a BitEncoding contains info to translate from a FormulaSet to an EncodedAtom and viceversa
data BitEncoding = BitEncoding
  { fetch :: (Int -> Formula APType)
  , index :: (Formula APType -> Int)
  , width :: Int
  , propBits :: Int
  , maskProps :: EncodedAtom -- EncodedAtom containing all APs
  }

newBitEncoding :: (Int -> Formula APType)
               -> (Formula APType -> Int)
               -> Int
               -> Int
               -> BitEncoding
newBitEncoding fetch_ index_ width_ propBits_ =
  BitEncoding fetch_ index_ width_ propBits_ maskProps_
  where maskProps_ = EncodedAtom $ BV.ones propBits_

-- an encoded atom is just a bitset
newtype EncodedAtom = EncodedAtom BitVector deriving (Eq, Ord, Show)

instance Hashable EncodedAtom where
  hashWithSalt salt (EncodedAtom bv) = hashWithSalt salt $ BV.nat bv

--- decode a BitVector into a plain set of formulas
decode :: BitEncoding -> EncodedAtom -> FormulaSet
decode bitenc (EncodedAtom bv) =
  let pos = map (fetch bitenc) (listBits bv) -- all the positive formulas, according to the bitencoding
      neg = map (Not . (fetch bitenc)) (listBits . BV.complement $ bv) -- all the negative formulas, according to the bitencoding
  in S.fromList pos `S.union` S.fromList neg

-- decode a BitVector into a plain set of formulas, keeping only positive formulas
pdecode :: BitEncoding -> EncodedAtom -> FormulaSet
pdecode bitenc (EncodedAtom bv) =
  S.fromList $ map (fetch bitenc) (listBits bv)
{-# INLINABLE pdecode #-}

-- encode a set of formulas into an EncodedAtom
encode :: BitEncoding -> FormulaSet -> EncodedAtom
encode bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ width bitenc) (S.map (index bitenc) set)
{-# INLINABLE encode #-}

-- encode a single formula into an EncodedAtom
singleton :: BitEncoding -> Formula APType -> EncodedAtom
singleton bitenc f | negative f = error "Cannot make singleton with negative formula."
                   | otherwise = EncodedAtom $ BV.setBit (BV.zeros $ width bitenc) (index bitenc $ f)
{-# INLINABLE singleton #-}

empty :: BitEncoding -> EncodedAtom
empty bitenc = EncodedAtom . BV.zeros $ width bitenc
{-# INLINABLE empty #-}


-- generate the powerset of the Formula parts of EncodedAtoms
-- must be concatenated with an encoded Input to make an entire EncodedAtom
generateFormulas :: BitEncoding -> [EncodedAtom]
generateFormulas bitenc =
  let len = width bitenc - propBits bitenc
  in if len == 0
     then []
     else map (EncodedAtom . BV.reverse) $ BV.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
{-# INLINABLE generateFormulas #-}

-- power set of a list of formulas as a list of EncodedAtoms
powerSet :: BitEncoding -> [Formula APType] -> [EncodedAtom]
powerSet bitenc fs =
  foldM (\set f -> [set, set `union` (singleton bitenc f)]) (empty bitenc) fs

-- test whether the given EncodedAtom is empty
null :: EncodedAtom -> Bool
null (EncodedAtom bv) = bv == BV.nil
{-# INLINE null #-}

-- test whether all bits are set in the given EncodedAtom
all :: EncodedAtom -> Bool
all (EncodedAtom bv) = bv == BV.ones (BV.size bv)

-- test whether a Formula is part of an EncodedAtom
member :: BitEncoding -> Formula APType -> EncodedAtom -> Bool
member bitenc phi (EncodedAtom bv) | negative phi = not $ bv BV.@. (index bitenc $ negation phi)
                                   | otherwise = bv BV.@. (index bitenc $ phi)
{-# INLINABLE member #-}

-- test whether any formula in EncodedAtom satisfies the predicate
any :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> Bool
any bitenc predicate (EncodedAtom bv) = Prelude.any (predicate . (fetch bitenc)) $ listBits bv
{-# INLINABLE any #-}

-- filter the formulas in an EncodedAtom according to predicate
filter :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> EncodedAtom
filter bitenc predicate (EncodedAtom bv) =
  EncodedAtom . snd $ BV.foldr filterVec (0, BV.zeros $ BV.width bv) bv
  where filterVec b (i, acc) = if b && predicate (fetch bitenc $ i)
                               then (i+1, BV.setBit acc i)
                               else (i+1, acc)
{-# INLINABLE filter #-}

-- get an EncodedAtom containing formulas which satisfy the given predicate
suchThat :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom
suchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = width bitenc
        bitList = map (predicate . (fetch bitenc)) [(len-1), (len-2)..0]
{-# INLINABLE suchThat #-}

-- bitwise AND between two BitVectors
intersect :: EncodedAtom -> EncodedAtom -> EncodedAtom
intersect (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .&. v2
{-# INLINE intersect #-}

-- bitwise OR between two BitVectors
union :: EncodedAtom -> EncodedAtom -> EncodedAtom
union (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .|. v2
{-# INLINE union #-}

-- returns the concatenation of two EncodedAtoms
joinInputFormulas :: EncodedAtom -> EncodedAtom -> EncodedAtom
joinInputFormulas (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v2 BV.# v1
{-# INLINABLE joinInputFormulas #-}

-- filter APs in EncodedAtom
extractInput :: BitEncoding -> EncodedAtom -> EncodedAtom
extractInput bitenc ea = intersect ea (maskProps bitenc)
{-# INLINABLE extractInput #-}

sliceInput :: BitEncoding -> EncodedAtom -> EncodedAtom
sliceInput bitenc (EncodedAtom v) = EncodedAtom $ BV.least (propBits bitenc) v
{-# INLINABLE sliceInput #-}

-- get the set of APs from an EncodedAtom
decodeInput :: BitEncoding -> EncodedAtom -> PropSet
decodeInput bitenc (EncodedAtom bv) =
  S.fromList $ map (getProp . (fetch bitenc)) (listBits bv)
  where getProp (Atomic p) = p
        getProp _ = error "Input contains non-atomic formulas!"
{-# INLINABLE decodeInput #-}

-- given a BitEncoding, encode a set of APs into an EncodedAtom
encodeInput :: BitEncoding -> PropSet -> EncodedAtom
encodeInput bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ propBits bitenc) (S.map (index bitenc . Atomic) set)
{-# INLINABLE encodeInput #-}

-- get an EncodedAtom containing APs which satisfy the given predicate
-- (same as suchThat, but only considers APs)
inputSuchThat :: BitEncoding -> (Prop APType -> Bool) -> EncodedAtom
inputSuchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = propBits bitenc
        bitList = map (atomicPred . (fetch bitenc)) [(len-1), (len-2)..0]
        atomicPred (Atomic p) = predicate p
        atomicPred _ = error "Expected atomic formula, got something else."
{-# INLINABLE inputSuchThat #-}

-- encode a single formula into an EncodedAtom
singletonInput :: BitEncoding -> Prop APType -> EncodedAtom
singletonInput bitenc f =
  EncodedAtom $ BV.setBit (BV.zeros $ propBits bitenc) (index bitenc $ Atomic f)
{-# INLINABLE singletonInput #-}

-- generate all possible input sets
generateInputs :: BitEncoding -> [Prop APType] -> [Prop APType] -> [EncodedAtom]
generateInputs bitenc sls als =
  let alSets = foldM
               (\set f -> [set, set `union` (singletonInput bitenc f)])
               (EncodedAtom . BV.zeros . propBits $ bitenc)
               als
      nonEnd = concatMap (\sl -> map (`union` (singletonInput bitenc sl)) alSets) sls
  in (singletonInput bitenc End) : nonEnd

-- list of all set bits in a BitVector
listBits :: BitVector -> [Int]
listBits v = snd $ BV.foldr (\b (i, l) -> if b then (i+1, i:l) else (i+1, l)) (0, []) v

nat :: EncodedAtom -> Int
nat (EncodedAtom bv) = fromInteger . BV.nat $ bv
