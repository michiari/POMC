{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                                ) where
import Prelude
import Pomc.Prob.ProbUtils
import Pomc.Prob.SummaryChain
import Pomc.Prec (Prec(..),)
import Pomc.Check (EncPrecFunc)


import Data.Hashable(Hashable)
import qualified Data.Set as Set
import Data.Maybe(fromJust, isJust, isNothing)

import Z3.Monad

import Control.Monad (foldM)
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
        -> IO (Maybe Rational, String)
terminationQuery summChain e p = evalZ3 $ terminationProbability summChain e p

-- compute the probabilities that a chain will terminate
-- assumption: the initial state is at position 0
terminationProbability :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> EncPrecFunc
        -> Prob -- is  the termination prob. of the initial state smaller or equal than this bound?
        -> Z3 (Maybe Rational, String)
terminationProbability chain precFun bound =
  let encode [] _ debugMsg = return debugMsg
      encode ((gnId_, rightContext):unencoded) varMap debugMsg = do
        var <- liftIO . stToIO $ fromJust <$> BH.lookup varMap (gnId_, rightContext)
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating states -> probability 1)
              | isNothing g && (gnId_ /= 0) = do
                  as <- mkEq var =<< mkRealNum (1 :: Prob)
                  assert as
                  asString <- astToString as
                  return ([], asString)

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush chain varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take =
                  encodePop chain gn rightContext var
                
              | otherwise = fail "unexpected prec rel"

        (new_unencoded, msg) <- cases
        encode (new_unencoded ++ unencoded) varMap (debugMsg ++ ".........." ++ msg)
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)"
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var -- by convention, we give rightContext -1 to the initial state
    debugMsg <- encode [(0 ::Int , -1 :: Int)] newVarMap "" -- encode the probability transition relation via a set of assertions
    assert =<< mkLe new_var =<< mkRealNum bound -- assert the inequality constrain
    termProb <- fmap snd . withModel $ \m -> fromJust <$> evalReal m new_var
    return (termProb, debugMsg)
                              

encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], String)
encodePush chain varMap gn rightContext var =
  let closeSummaries pushGn (currs, unencoded_vars) e = do
        summaryGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        let varsIds = [(gnId pushGn, getId . fst . node $ summaryGn), (gnId summaryGn, rightContext)]
        vars <- mapM (lookupVar varMap) varsIds
        eq <- mkMul (map fst vars)
        return (eq:currs, 
              [(gnId_, rightContext_) | ((_,alrEncoded), (gnId_, rightContext_)) <- zip vars varsIds, not alrEncoded] ++ unencoded_vars)
      pushEnc (currs, new_vars) e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        (equations, unencoded_vars) <- foldM (closeSummaries toGn) ([], []) (summaryEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        return (transition:currs, unencoded_vars ++ new_vars)
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    as <- mkEq var =<< mkAdd transitions -- assert the equation for this semiconf
    assert as
    asString <- astToString as
    return (unencoded_vars, asString)

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap RealWorld
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], String)
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (toVar, alreadyEncoded) <- lookupVar varMap (to e, rightContext)
        trans <- encodeTransition e toVar
        return (trans:currs, if alreadyEncoded then new_vars else (to e, rightContext):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    as <- mkEq var =<< mkAdd transitions -- assert the equation for this semiconf
    assert as
    asString <- astToString as
    return (unencoded_vars, asString)

encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], String)
encodePop chain gn rightContext var =
  let checkEdge e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        return $ rightContext == (getId . fst . node $ toGn)
      matchContext [] = return (0 :: Prob)
      matchContext (e:es) = do 
        found <- checkEdge e 
        if found
          then return (prob e)
          else matchContext es
  in do
    -- assert the equation for this semiconf
    as <- mkEq var =<< mkRealNum =<< matchContext (Set.toList $ internalEdges gn)
    assert as
    asString <- astToString as
    return ([], asString) -- pop transitions do not generate new variables

