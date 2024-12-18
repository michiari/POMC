{- |
   Module      : Pomc ProbEncoding
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbEncoding( ProBitencoding
                         , ProbEncodedSet
                         , makeProBitEncoding
                         , empty
                         , null
                         , union
                         , unions
                         , encodeSatState
                         , subsumes
                         , isSatisfying
                         , showProbEncoding
                         ) where

import Prelude hiding (null)
import Pomc.Check(makeBitEncoding, isNotTrivialOmega)
import Pomc.Potl (Formula)
import Pomc.Encoding (BitEncoding, EncodedSet)
import qualified Pomc.Encoding as E
import Pomc.PropConv(APType)
import Pomc.State(State)
import Pomc.SatUtil(SatState, getSatState)
import Data.List (foldl')


-- data structures for keeping track of satisfied formulae in the probabilistic model checking algorithm. 
type ProbEncodedSet = EncodedSet

data ProBitencoding = ProBitEncoding
  { bitenc :: BitEncoding
  , isPhiFinal :: Formula APType -> State -> Bool
  }

makeProBitEncoding :: [Formula APType] -> (Formula APType -> State -> Bool) -> ProBitencoding
makeProBitEncoding cl isPhiFinal_ =
   ProBitEncoding{ bitenc = makeBitEncoding (filter isNotTrivialOmega  cl)
                       , isPhiFinal = isPhiFinal_
                       }

-- an empty EncodedSet
empty :: ProBitencoding -> ProbEncodedSet
empty probitenc = E.empty (bitenc probitenc)

-- Is the Encoded set null?
null :: ProbEncodedSet -> Bool
null = E.null

-- bitwise OR between two BitVectors
union ::  ProbEncodedSet -> ProbEncodedSet -> ProbEncodedSet
union = E.union

-- a helper for bitwise OR between multiple BitVectors
-- requires: the input list must be non empty
unions ::  [ProbEncodedSet] -> ProbEncodedSet
unions [] = error "unions of empty list"
unions [x] = x
unions l = foldl' union (head l) (tail l)

-- encode a satState into the formulae for which this state is final
encodeSatState :: (SatState state) => ProBitencoding -> state -> ProbEncodedSet
encodeSatState probitenc s = E.suchThat (bitenc probitenc) (\f -> (isPhiFinal probitenc) f (getSatState s))

subsumes :: ProbEncodedSet -> ProbEncodedSet -> Bool
subsumes eset1 eset2 = E.union eset1 eset2 == eset1

-- are all formulae satisfied?
isSatisfying :: EncodedSet -> Bool
isSatisfying = E.allSet

-- for debugging purposes
showProbEncoding :: ProBitencoding -> ProbEncodedSet -> String
showProbEncoding probitenc e = "SatFormulae [" ++ show (E.decode (bitenc probitenc) e) ++ "]"
