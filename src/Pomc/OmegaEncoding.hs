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
                         , encodeSatState
                         , implies
                         , isSatisfying
                         , showOmegaEncoding
                         ) where

import Pomc.Check(makeBitEncoding, isNotTrivialOmega)
import Pomc.Potl (Formula)
import Pomc.Encoding (BitEncoding, EncodedSet, FormulaSet)
import qualified Pomc.Encoding as E
import Pomc.PropConv(APType)
import Pomc.State(State)
import Pomc.SatUtil(SatState, getSatState)
import Data.List (foldl')


-- a data structure for keeping track of satisfied formulae in the omega SCC algorithm. 
-- strictly resembling the bitencoding for formulae holding in a state
-- the two data constructors record whether a sat state for the input model has been visited
data OmegaEncodedSet = SatModel {eset :: EncodedSet} | UnsatModel {eset :: EncodedSet}
   deriving (Eq, Ord, Show)

data OmegaBitencoding state = OmegaBitEncoding
  { bitenc :: BitEncoding
  , isModelFinal :: state -> Bool
  , isPhiFinal :: Formula APType -> State -> Bool
  }

makeOmegaBitEncoding :: [Formula APType] -> (state -> Bool) -> (Formula APType -> State -> Bool) -> OmegaBitencoding state
makeOmegaBitEncoding cl isModelFinal_ isPhiFinal_ = 
   OmegaBitEncoding{ bitenc = makeBitEncoding (filter isNotTrivialOmega cl)
                   , isModelFinal = isModelFinal_
                   , isPhiFinal = isPhiFinal_
                   }

-- an empty EncodedSet
empty :: OmegaBitencoding state -> OmegaEncodedSet
empty omegabitenc = UnsatModel (E.empty (bitenc omegabitenc))

-- bitwise OR between two BitVectors
union ::  OmegaEncodedSet -> OmegaEncodedSet -> OmegaEncodedSet
union (UnsatModel ea1) (UnsatModel ea2) = UnsatModel (E.union ea1 ea2)
union oset1 oset2 = SatModel (E.union (eset oset1) (eset oset2))
{-# INLINE union #-}

-- a helper for bitwise OR between multiple BitVectors
-- requires: the input list must be non empty
unions :: [OmegaEncodedSet] -> OmegaEncodedSet
unions l = foldl' union (head l) (tail l)

-- encode a set of formulas into an EncodedAtom
encode :: OmegaBitencoding state -> FormulaSet -> state -> OmegaEncodedSet
encode omegabitenc set state 
 | (isModelFinal omegabitenc) state = SatModel eatom
 | otherwise = UnsatModel eatom
    where eatom = E.encode (bitenc omegabitenc) set

-- encode a satState into the formulae for which this state is final
encodeSatState :: (SatState state) => OmegaBitencoding state -> state -> OmegaEncodedSet
encodeSatState omegabitenc s 
 | (isModelFinal omegabitenc) s = SatModel eatom
 | otherwise = UnsatModel eatom 
   where eatom = E.suchThat (bitenc omegabitenc) (\f -> (isPhiFinal omegabitenc) f (getSatState s))

implies :: OmegaEncodedSet -> OmegaEncodedSet -> Bool 
implies (UnsatModel _) (SatModel _)  = False
implies oset1 oset2 = E.union (eset oset1) (eset oset2) == (eset oset1)

-- are all formulae satisfied?
isSatisfying :: OmegaEncodedSet -> Bool 
isSatisfying (UnsatModel _) = False 
isSatisfying (SatModel ea) = E.all ea

-- for debugging purposes
showOmegaEncoding :: OmegaBitencoding state -> OmegaEncodedSet -> String
showOmegaEncoding omegabitenc (SatModel e) = "SatModel [" ++ show (E.decode (bitenc omegabitenc) e) ++ "]"
showOmegaEncoding omegabitenc (UnsatModel e) = "UnsatModel [" ++ show (E.decode (bitenc omegabitenc) e) ++ "]"
   