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
                 , EncodedAtom
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
                 , EncodedState
                 , newEncodedState
                 , currToAtom
                 , pendToAtom
                 , getXl
                 , getXe
                 , getXr
                 ) where

import Pomc.Prop (Prop)
import Pomc.RPotl
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

data BitEncoding = BitEncoding
  { fetch :: (Int -> Formula APType)
  , index :: (Formula APType -> Int)
  , formulaBits :: Int
  , propBits :: Int
  , atomWidth :: Int
  , maskProps :: BitVector
  , maskFormulas :: BitVector
  , maskAtom :: BitVector
  }

newBitEncoding :: (Int -> Formula APType)
               -> (Formula APType -> Int)
               -> Int
               -> Int
               -> BitEncoding
newBitEncoding fetch_ index_ formulaBits_ propBits_ =
  BitEncoding { fetch = fetch_
              , index = index_
              , formulaBits = formulaBits_
              , propBits = propBits_
              , atomWidth = formulaBits_ + propBits_
              , maskProps = maskProps_
              , maskFormulas = complement $ BV.zeroExtend formulaBits_ maskProps_
              , maskAtom = BV.ones $ formulaBits_ + propBits_
              }
  where maskProps_ = BV.ones propBits_

newtype EncodedAtom = EncodedAtom BitVector deriving (Eq, Ord, Show)

instance Hashable EncodedAtom where
  hashWithSalt salt (EncodedAtom bv) = hashWithSalt salt $ BV.nat bv


decode :: BitEncoding -> EncodedAtom -> FormulaSet
decode bitenc (EncodedAtom bv) =
  let atom = BV.least (atomWidth bitenc) bv
      pos = map (fetch bitenc) (listBits atom)
      neg = map (Not . (fetch bitenc)) (listBits . BV.complement $ atom)
  in S.fromList pos `S.union` S.fromList neg

pdecode :: BitEncoding -> EncodedAtom -> FormulaSet
pdecode bitenc (EncodedAtom bv) =
  S.fromList $ map (fetch bitenc) (listBits $ BV.least (atomWidth bitenc) bv)
{-# INLINABLE pdecode #-}

encode :: BitEncoding -> FormulaSet -> EncodedAtom
encode bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ atomWidth bitenc) (S.map (index bitenc) set)
{-# INLINABLE encode #-}

singleton :: BitEncoding -> Formula APType -> EncodedAtom
singleton bitenc f =
  EncodedAtom $ BV.setBit (BV.zeros $ atomWidth bitenc) (index bitenc $ f)
{-# INLINABLE singleton #-}

empty :: BitEncoding -> EncodedAtom
empty bitenc = EncodedAtom . BV.zeros $ atomWidth bitenc
{-# INLINABLE empty #-}

generateFormulas :: BitEncoding -> [EncodedAtom]
generateFormulas bitenc =
  let len = atomWidth bitenc - propBits bitenc
  in if len == 0
     then []
     else map (EncodedAtom . BV.reverse) $ BV.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
{-# INLINABLE generateFormulas #-}

null :: EncodedAtom -> Bool
null (EncodedAtom bv) = bv == BV.nil
{-# INLINE null #-}

member :: BitEncoding -> Formula APType -> EncodedAtom -> Bool
member bitenc phi (EncodedAtom bv) | negative phi = not $ bv BV.@. (index bitenc $ negation phi)
                                   | otherwise = bv BV.@. (index bitenc $ phi)
{-# INLINABLE member #-}

any :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> Bool
any bitenc predicate (EncodedAtom bv) = Prelude.any (predicate . (fetch bitenc)) $ listBits bv
{-# INLINABLE any #-}

filter :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom -> EncodedAtom
filter bitenc predicate (EncodedAtom bv) = EncodedAtom . snd $ BV.foldr filterVec (0, BV.zeros $ BV.width atom) atom
  where filterVec b (i, acc) = if b && predicate (fetch bitenc $ i)
                               then (i+1, BV.setBit acc i)
                               else (i+1, acc)
        atom = BV.least (atomWidth bitenc) bv
{-# INLINABLE filter #-}

suchThat :: BitEncoding -> (Formula APType -> Bool) -> EncodedAtom
suchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = atomWidth bitenc
        bitList = map (predicate . (fetch bitenc)) [(len-1), (len-2)..0]
{-# INLINABLE suchThat #-}

intersect :: EncodedAtom -> EncodedAtom -> EncodedAtom
intersect (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .&. v2
{-# INLINE intersect #-}

union :: EncodedAtom -> EncodedAtom -> EncodedAtom
union (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v1 .|. v2
{-# INLINE union #-}

joinInputFormulas :: EncodedAtom -> EncodedAtom -> EncodedAtom
joinInputFormulas (EncodedAtom v1) (EncodedAtom v2) = EncodedAtom $ v2 BV.# v1
{-# INLINABLE joinInputFormulas #-}

extractInput :: BitEncoding -> EncodedAtom -> EncodedAtom
extractInput bitenc (EncodedAtom bv) = EncodedAtom $ bv .&. maskProps bitenc
{-# INLINABLE extractInput #-}

decodeInput :: BitEncoding -> EncodedAtom -> PropSet
decodeInput bitenc (EncodedAtom bv) =
  S.fromList $ map (getProp . (fetch bitenc)) (listBits $ BV.least (propBits bitenc) bv)
  where getProp (Atomic p) = p
{-# INLINABLE decodeInput #-}

encodeInput :: BitEncoding -> PropSet -> EncodedAtom
encodeInput bitenc set =
  EncodedAtom $ S.foldl BV.setBit (BV.zeros $ propBits bitenc) (S.map (index bitenc . Atomic) set)
{-# INLINABLE encodeInput #-}

inputSuchThat :: BitEncoding -> (Prop APType -> Bool) -> EncodedAtom
inputSuchThat bitenc predicate = EncodedAtom $ BV.fromBits bitList
  where len = propBits bitenc
        bitList = map (atomicPred . (fetch bitenc)) [(len-1), (len-2)..0]
        atomicPred (Atomic p) = predicate p
{-# INLINABLE inputSuchThat #-}


listBits :: BitVector -> [Int]
listBits v = snd $ BV.foldr (\b (i, l) -> if b then (i+1, i:l) else (i+1, l)) (0, []) v


newtype EncodedState = EncodedState BitVector deriving (Eq, Ord, Show)

instance Hashable EncodedState where
  hashWithSalt salt (EncodedState bv) = hashWithSalt salt $ BV.nat bv

newEncodedState :: BitEncoding
                -> EncodedAtom
                -> EncodedAtom
                -> Bool
                -> Bool
                -> Bool
                -> EncodedState
newEncodedState bitenc (EncodedAtom curr) (EncodedAtom pend) xl xe xr =
  let bv | formulaBits bitenc == 0 = (BV.fromBits [xl, xe, xr]) BV.# curr
         | otherwise = {-# SCC "newEncodedState:xs" #-} (BV.fromBits [xl, xe, xr])
                       BV.# {-# SCC "newEncodedState:pend" #-} (pend BV.@@ (atomWidth bitenc - 1, propBits bitenc))
                                                        BV.# curr
  in EncodedState bv

currToAtom :: BitEncoding -> EncodedState -> EncodedAtom
currToAtom bitenc (EncodedState bv) = EncodedAtom $ BV.least (atomWidth bitenc) bv
-- We should zero-out bits higher than atomWidth, but we do not, for performance's sake.

pendToAtom :: BitEncoding -> EncodedState -> EncodedAtom
pendToAtom bitenc (EncodedState bv) =
  EncodedAtom $
  (bv BV.@@ (atomWidth bitenc + formulaBits bitenc - 1, formulaBits bitenc))
  .&. (maskFormulas bitenc)
-- We should zero-out propositional bits, but we do not, for performance's sake.

getXl :: BitEncoding -> EncodedState -> Bool
getXl bitenc (EncodedState bv) = bv BV.@. (atomWidth bitenc + formulaBits bitenc + 2)

getXe :: BitEncoding -> EncodedState -> Bool
getXe bitenc (EncodedState bv) = bv BV.@. (atomWidth bitenc + formulaBits bitenc + 1)

getXr :: BitEncoding -> EncodedState -> Bool
getXr bitenc (EncodedState bv) = bv BV.@. (atomWidth bitenc + formulaBits bitenc)
