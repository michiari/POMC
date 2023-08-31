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

import Data.List (nub)
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
encodeTransition e to = do 
  prob <- mkRealNum (toI e)
  mkMul [to, prob]

lookupVar :: VarMap RealWorld -> (Int, Int) -> Z3 (AST, Bool)
lookupVar varMap key = do 
  maybeVar <- liftIO . stToIO $ BH.lookup varMap key 
  if isJust maybeVar 
    then return (fromJust maybeVar, True)
    else do 
      new_var <- mkFreshRealVar $ show key
      liftIO . stToIO $ BH.insert varMap key new_var
      return (new_var, False)

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap RealWorld
        -> GraphNode state
        -> StateId state 
        -> AST
        -> Z3 (AST, [AST])
encodeShift varMap gn rightContext var = 
  let shiftEnc (currs, new_vars) e = do 
        (var, alreadyEncoded) <- lookupVar varMap (toI e, getId rightContext)
        trans <- encodeTransition e var
        return (trans:currs, if alreadyEncoded then new_vars else var:new_vars)            
  in do 
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions
    return (equation, unencoded_vars) -- TODO: maybe add a safety check for duplicates in encoded_vars here


encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> StateId state 
        -> AST
        -> Z3 (AST, [AST])
encodePop chain gn rightContext var = 
  let popEnc acc e = do 
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (toI e)
        if rightContext == (fst . node $ toGn)
          then return $ acc + (probI e) -- TODO: can this happen? Can we have multiple pops that go the same state p?
          else return acc
  in do 
    equation <- mkEq var =<< mkRealNum =<< foldM popEnc (0 :: Prob) (internalEdges gn)
    return (equation, []) -- pop transitions do not generate new variables

encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap RealWorld
        -> GraphNode state
        -> StateId state 
        -> AST
        -> Z3 (AST, [AST])
encodePush chain varMap gn rightContext var = 
  let closeSummaries pushedGn (currs, new_vars) e = do
        summaryGn <- liftIO . stToIO $ MV.unsafeRead chain (toS e)
        vars <- mapM (lookupVar varMap) [(gnId pushedGn, getId . fst . node $ summaryGn), (gnId summaryGn, getId rightContext)]
        eq <- mkMul (map fst vars)
        return (eq:currs, [x | (x,y) <- vars, not y] ++ new_vars)
      pushEnc (currs, new_vars) e = do 
        pushedGn <- liftIO . stToIO $ MV.unsafeRead chain (toI e)
        (equations, unencoded_vars) <- foldM (closeSummaries pushedGn) ([], []) (summaryEdges gn) 
        transition <- encodeTransition e =<< mkAdd equations   
        return (transition:currs, unencoded_vars ++ new_vars)
  in do 
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions
    return (equation, nub unencoded_vars) -- TODO: can we remove the safety check nub?