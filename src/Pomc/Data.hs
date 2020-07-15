{-# LANGUAGE FlexibleInstances #-}

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
import Pomc.PropConv (APType)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Vector.Unboxed (Vector(..))
import qualified Data.Vector.Unboxed as VU

import Data.Bit (Bit)
import qualified Data.Bit as B

import GHC.Generics (Generic)
import Data.Hashable

instance Hashable Bit

instance Hashable (Vector Bit) where
  hashWithSalt salt vb = VU.foldl' (\acc v -> hashWithSalt acc v) salt words
    where words = B.cloneToWords vb

type EncodedSet = Vector Bit
type FormulaSet = Set (Formula APType)

decodeAtom :: (Int -> Formula APType) -> EncodedSet -> FormulaSet
decodeAtom fetch bv = let pos = map fetch (B.listBits bv)
                          neg = map (Not . fetch) (B.listBits . B.invertBits $ bv)
                      in S.fromList pos `S.union` S.fromList neg

encode :: (Formula APType -> Int) -> Int -> FormulaSet -> EncodedSet
encode lookup len set = let zeroes = VU.replicate len (B.Bit False)
                            pairs = S.toList $ S.map (\phi -> (lookup phi, B.Bit True)) set
                        in zeroes VU.// pairs

generate :: Int -> [Vector Bit]
generate len = VU.replicateM len [B.Bit False, B.Bit True]
