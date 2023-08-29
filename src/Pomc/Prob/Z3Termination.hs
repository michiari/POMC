{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationProbs
                                ) where

import Pomc.Prob.ProbUtils
import Pomc.Prob.SummaryChain
import Data.Hashable(Hashable)

import Control.Monad (foldM, filterM)

import Data.Maybe(fromJust, isJust)

import Z3.Monad
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO, RealWorld)

-- 
import qualified Data.Vector.Mutable as MV

import qualified Data.HashTable.ST.Basic as BH
-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v


-- a map (GraphNode, StateId) to Z3 variables
-- each variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode
-- and p is the state associated with the given StateId
type VarMap s = HashTable s (Int,Int) AST

-- compute the probabilities that a chain will terminate
-- assumption: the initial state is at position 0
terminationProbs :: (Eq state, Hashable state, Show state)
        => SummaryChain s state 
        -> [Prob]
terminationProbs = const []

encodeTransition :: InternalEdge -> AST -> Z3 AST 
encodeTransition e toVar = do 
  prob <- mkRealNum (toI e)
  mkMul [toVar, prob]


encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap RealWorld
        -> GraphNode state
        -> StateId state 
        -> AST
        -> Z3 (AST, [AST])
encodeShift vars gn leftContext var = 
  let 
    shiftEnc (currs, new_vars) e = do 
      maybevar <- liftIO . stToIO $ BH.lookup vars (toI e, getId leftContext)
      if isJust maybevar
        then do 
          trans <- encodeTransition e (fromJust maybevar) 
          return (trans:currs, new_vars)
        else do 
          new_var <- mkFreshRealVar $ show (gn, leftContext)
          liftIO . stToIO $ BH.insert vars (toI e, getId leftContext) new_var
          trans <- encodeTransition e new_var 
          return (trans:currs, new_var:new_vars)            
  in do 
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions
    return (equation, unencoded_vars)


encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> StateId state 
        -> AST
        -> Z3 (AST, [AST])
encodePop chain gn leftContext var = 
  let 
    popEnc acc e = do 
      gn <- liftIO . stToIO $ MV.unsafeRead chain (toI e)
      if leftContext == (fst . node $ gn)
        then return $ acc + (probI e)
        else return acc
  in do 
    equation <- mkEq var =<< mkRealNum =<< foldM popEnc (0 :: Double) (internalEdges gn)
    return (equation, []) -- pop transitions do not generate new variables

