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

import qualified Data.Set as Set
import Data.Maybe(fromJust, isJust, isNothing)

import Z3.Monad
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO, RealWorld)

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
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

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
        -> Prob
        -> IO (Maybe Rational)
terminationQuery summChain e p = evalZ3 $ terminationProbability summChain e p

-- compute the probabilities that a chain will terminate
-- assumption: the initial state is at position 0
terminationProbability :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> EncPrecFunc
        -> Prob -- is  the termination prob. of the initial state smaller or equal than this bound?
        -> Z3 (Maybe Rational)
terminationProbability chain precFun bound =
  let encode [] _ = return ()
      encode ((gnId_, rightContext, var):unencoded) varMap = do
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating states -> probability 1)
              | isNothing g && (gnId_ /= 0) = do
                  assert =<< mkEq var =<< mkRealNum (1 :: Prob)
                  return []

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush chain varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take =
                  encodePop chain gn rightContext var
                
              | otherwise = fail "unexpected prec rel"

        new_unencoded <- cases
        encode (new_unencoded ++ unencoded) varMap
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)"
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var -- by convention, we give rightContext -1 to the initial state
    encode [(0 ::Int , -1 :: Int, new_var)] newVarMap --encode the probabilistic transition relation
    assert =<< mkLe new_var =<< mkRealNum bound -- assert the inequality constrain
    fmap snd . withModel $ \m -> fromJust <$> evalReal m new_var

encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 [(Int, Int, AST)]
encodePush chain varMap gn rightContext var =
  let closeSummaries pushedGn (currs, unencoded_vars) e = do
        summaryGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        let varsIds = [(gnId pushedGn, getId . fst . node $ summaryGn), (gnId summaryGn, rightContext)]
        vars <- mapM (lookupVar varMap) varsIds
        eq <- mkMul (map fst vars)
        return (eq:currs, [(gnId_, rightContext_, x) | ((x,alrEncoded), (gnId_, rightContext_)) <- zip vars varsIds, not alrEncoded] ++ unencoded_vars)
      pushEnc (currs, new_vars) e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        (equations, unencoded_vars) <- foldM (closeSummaries toGn) ([], []) (summaryEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        return (transition:currs, unencoded_vars ++ new_vars)
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    assert =<< mkEq var =<< mkAdd transitions
    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 [(Int, Int, AST)]
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (toVar, alreadyEncoded) <- lookupVar varMap (to e, rightContext)
        trans <- encodeTransition e toVar
        return (trans:currs, if alreadyEncoded then new_vars else (to e, rightContext, toVar):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    assert =<< mkEq var =<< mkAdd transitions
    return unencoded_vars

encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 [(Int, Int, AST)]
encodePop chain gn rightContext var =
  let matchContext e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        return $ rightContext == (getId . fst . node $ toGn)
  in do
    -- TODO: can we have multiple pops that go to the same rightContext?
    assert =<< mkEq var =<< mkRealNum =<< sum . map prob <$> filterM matchContext (Set.toList $ internalEdges gn)
    return [] -- pop transitions do not generate new variables

