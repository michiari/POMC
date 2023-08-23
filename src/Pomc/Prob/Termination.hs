{- |
   Module      : Pomc.Prob.Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Termination ( terminationProbs
                                ) where

import Data.Hashable(Hashable)
import Pomc.Encoding(BitEncoding)
import Pomc.Check(EncPrecFunc)
import Pomc.SatUtil

import Z3.Monad

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v




data Z3Var state = Z3Var 
  { var :: AST
  , semiconf :: (StateId state, Stack state)
  , evaluation :: Double
  }

instance Show (Z3Var state) where 
  show v = show $ var v

-- compute the probabilities that a chain will terminate
terminationProbs :: (SatState state, Eq state, Hashable state, Show state)
        => state -- initial state of the popa
        -> [Double]
terminationProbs initial = []
  
  
  