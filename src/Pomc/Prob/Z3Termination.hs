{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                                ) where

import Pomc.Prob.ProbUtils
import Pomc.Prob.SummaryChain
import Data.Hashable(Hashable)

import Control.Monad (foldM, filterM)

import Pomc.Prec (Prec(..),)
import Pomc.Check (EncPrecFunc)


import Data.Maybe(fromJust, isJust, isNothing)

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


--helpers
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
-- end helpers

terminationQuery ::(Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> EncPrecFunc
        -> Prob -- is  the termination prob. of the initial state smaller or equal than the given initial state?
        -> IO (Maybe Rational)
terminationQuery s e p = evalZ3 $ terminationProbability s e p

-- compute the probabilities that a chain will terminate
-- assumption: the initial state is at position 0
terminationProbability :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> EncPrecFunc
        -> Prob -- is  the termination prob. of the initial state smaller or equal than the given initial state?
        -> Z3 (Maybe Rational)
terminationProbability chain prec prob =
  let encode acc [] _ = return acc
      encode acc ((gnId_, rightContext, var):unencoded) varMap = do
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = prec (fst . fromJust $ g) qLabel
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating states -> probability 1)
              | isNothing g && (getId q /= 0) =
                  (\a -> return (a, [])) =<< mkEq var =<< mkRealNum (1 :: Prob)

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush chain varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take =
                  encodePop chain gn rightContext var
                
              | otherwise = fail "unexpected prec rel"

        (a, new_unencoded) <- cases
        encode (a:acc) (new_unencoded ++ unencoded) varMap
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar $ show "(0,-1)"
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var -- by convention, we give rightContext -1 to the initial state
    encodings <- encode [] [(0 ::Int , -1 :: Int, new_var)] newVarMap
    inequality <- mkLe new_var =<< mkRealNum prob
    assert =<< mkAnd (inequality:[]) -- assert all the equations
    fmap snd . withModel $ \m -> fromJust <$> evalReal m new_var


encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 (AST, [(Int, Int, AST)])
encodePush chain varMap gn rightContext var =
  let closeSummaries pushedGn (currs, new_vars) e = do
        summaryGn <- liftIO . stToIO $ MV.unsafeRead chain (toS e)
        let varsIds = [(gnId pushedGn, getId . fst . node $ summaryGn), (gnId summaryGn, rightContext)]
        vars <- mapM (lookupVar varMap)  varsIds
        eq <- mkMul (map fst vars)
        return (eq:currs, [(g, con, x) | ((x,y), (g, con)) <- zip vars varsIds, not y] ++ new_vars)
      pushEnc (currs, new_vars) e = do
        pushedGn <- liftIO . stToIO $ MV.unsafeRead chain (toI e)
        (equations, unencoded_vars) <- foldM (closeSummaries pushedGn) ([], []) (summaryEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        return (transition:currs, unencoded_vars ++ new_vars)
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions
    return (equation, nub unencoded_vars) -- TODO: can we remove the safety check nub?

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 (AST, [(Int, Int, AST)])
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (var, alreadyEncoded) <- lookupVar varMap (toI e, rightContext)
        trans <- encodeTransition e var
        return (trans:currs, if alreadyEncoded then new_vars else (toI e, rightContext,var):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions
    return (equation, unencoded_vars) -- TODO: maybe add a safety check for duplicates in encoded_vars here


encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 (AST, [(Int, Int, AST)])
encodePop chain gn rightContext var =
  let popEnc acc e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (toI e)
        if rightContext == (getId . fst . node $ toGn)
          then return $ acc + (probI e) -- TODO: can this happen? Can we have multiple pops that go the same state p?
          else return acc
  in do
    equation <- mkEq var =<< mkRealNum =<< foldM popEnc (0 :: Prob) (internalEdges gn)
    return (equation, []) -- pop transitions do not generate new variables