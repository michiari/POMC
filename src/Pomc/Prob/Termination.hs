{- |
   Module      : Pomc.Prob.Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Termination ( terminationProbs
                                ) where

import Pomc.Prob.ProbUtils
import Pomc.Prob.SummaryChain(SummaryChain)
import Data.Hashable(Hashable)

import Z3.Monad

data Z3Var state = Z3Var 
  { var :: AST
  , exitPort :: StateId state
  }

instance Show (Z3Var state) where 
  show v = show $ var v

-- compute the probabilities that a chain will terminate
terminationProbs :: (Eq state, Hashable state, Show state)
        => SummaryChain s state-- initial state of the popa
        -> [Prob]
terminationProbs initial = []
  
  
  