{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.OmegaEncoding
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.OmegaEncoding( OmegaBitencoding
                         , OmegaEncodedSet
                         , makeOmegaBitEncoding
                         , empty
                         , union
                         , unions
                         , encode
                         , isSubset
                         , isSatisfying
                         ) where

import Pomc.Check(makeBitEncoding, isNotTrivialOmega)
import Pomc.Potl (Formula)
import Pomc.Encoding (BitEncoding, EncodedSet, FormulaSet)
import qualified Pomc.Encoding as E
import Pomc.PropConv(APType)
import Data.List (foldl')

-- a data structure for keeping track of satisfied formulae in the omega SCC algorithm. 
-- the two data constructors record whether a sat state for the input model has been visited
data OmegaEncodedSet = SatModel {eset :: EncodedSet} | UnsatModel {eset :: EncodedSet}

data OmegaBitencoding state = OmegaBitEncoding
  { bitenc :: BitEncoding
  , isModelFinal :: state -> Bool
  }

makeOmegaBitEncoding :: [Formula APType] -> (state -> Bool) -> OmegaBitencoding state
makeOmegaBitEncoding cl isModelFinal_ = OmegaBitEncoding{bitenc = makeBitEncoding (filter isNotTrivialOmega cl), isModelFinal = isModelFinal_}

-- an Empty EncodedSet
empty :: OmegaBitencoding state -> OmegaEncodedSet
empty omegabitenc = UnsatModel (E.empty (bitenc omegabitenc))
{-# INLINABLE empty #-}

-- bitwise OR between two BitVectors
union ::  OmegaEncodedSet -> OmegaEncodedSet -> OmegaEncodedSet
union (UnsatModel ea1) (UnsatModel ea2) = UnsatModel (E.union ea1 ea2)
union oset1 oset2 = SatModel (E.union (eset oset1) (eset oset2))
{-# INLINE union #-}

-- a helper for bitwise OR between multiple BitVectors
unions :: OmegaBitencoding state -> [OmegaEncodedSet] -> OmegaEncodedSet
unions omegabitenc = foldl' union (empty omegabitenc)

-- encode a set of formulas into an EncodedAtom
encode :: OmegaBitencoding state -> FormulaSet -> state -> OmegaEncodedSet
encode omegabitenc set state 
 | (isModelFinal omegabitenc) state = SatModel eatom
 | otherwise = UnsatModel eatom
    where eatom = E.encode (bitenc omegabitenc) set
{-# INLINABLE encode #-}

isSubset :: OmegaEncodedSet -> OmegaEncodedSet -> Bool 
isSubset (SatModel _) (UnsatModel _) = False
isSubset oset1 oset2 = E.union (eset oset1) (eset oset2) == (eset oset2)

isSatisfying :: OmegaEncodedSet -> Bool 
isSatisfying (UnsatModel _) = False 
isSatisfying (SatModel ea) = E.all ea
   