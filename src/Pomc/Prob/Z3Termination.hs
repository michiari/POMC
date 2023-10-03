{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                                ) where

import Prelude hiding (LT, GT)
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
import qualified Data.HashTable.Class as BC

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- a map (gnId GraphNode, getId StateId) to Z3 variables
-- each variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = HashTable RealWorld (Int,Int) AST

--helpers
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

lookupVar :: VarMap -> (Int, Int) -> Z3 (AST, Bool)
lookupVar varMap key = do
  maybeVar <- liftIO . stToIO $ BH.lookup varMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      new_var <- mkFreshRealVar $ show key
      liftIO . stToIO $ BH.insert varMap key new_var
      return (new_var, False)
-- end helpers


-- compute the probabilities that a chain will terminate
-- assumption: the initial state is at position 0
terminationQuery :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> EncPrecFunc
        -> TermQuery
        -> Z3 (TermResult, String)
terminationQuery chain precFun query =
  let encode [] _  eqs = return eqs
      encode ((gnId_, rightContext):unencoded) varMap eqs = do
        var <- liftIO . stToIO $ fromJust <$> BH.lookup varMap (gnId_, rightContext)
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating states -> probability 1)
              | isNothing g && (gnId_ /= 0) = do
                  equation <- mkEq var =<< mkRealNum (1 :: Prob)
                  return ([], equation)

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush chain varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take =
                  encodePop chain gn rightContext var
                
              | otherwise = fail "unexpected prec rel"

        (new_unencoded, eq) <- cases
        encode (new_unencoded ++ unencoded) varMap (eq:eqs)
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var 
    equations <- encode [(0 ::Int , -1 :: Int)] newVarMap [] -- encode the probability transition relation via a set of Z3 formulas represented via ASTs
    
    -- a string representation of the SMT Encoding for debugging purposes
    debugMsg <- foldM (\acc eq -> do 
      eqString <- astToString eq
      return (acc ++ eqString ++ "\n")
      ) 
      "" 
      equations
    encodeQuery query new_var equations newVarMap
    termRes <- computeResult query new_var 
    return (termRes, debugMsg)
                              
encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], AST)
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
    equation <- mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    return (unencoded_vars, equation)

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], AST)
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (toVar, alreadyEncoded) <- lookupVar varMap (to e, rightContext)
        trans <- encodeTransition e toVar
        return (trans:currs, if alreadyEncoded then new_vars else (to e, rightContext):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    return (unencoded_vars, equation)

encodePop :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], AST)
encodePop chain gn rightContext var =
  let checkEdge e = do
        toGn <- liftIO . stToIO $ MV.unsafeRead chain (to e)
        return $ rightContext == (getId . fst . node $ toGn)
      matchContext [] = return (0 :: Prob)
      matchContext (e:es) = do 
        found <- checkEdge e 
        if found
          then return (prob e) -- we return the probability of the first one matched
          else matchContext es
  in do
    -- generate the equation for this semiconf
    equation <- mkEq var =<< mkRealNum =<< matchContext (Set.toList $ internalEdges gn)
    return ([], equation) -- pop transitions do not generate new variables

encodeQuery :: TermQuery -> AST -> [AST] -> VarMap  -> Z3 ()
encodeQuery q
  | ApproxQuery <- q = encodeApproxQuery
  | (LT bound) <- q  = encodeComparison return mkExistsConst mkLt bound
  | (LE bound) <- q  = encodeComparison return mkExistsConst mkLe bound
  | (GT bound) <- q  = encodeComparison mkNot  mkExistsConst mkLe bound
  | (GE bound) <- q  = encodeComparison mkNot  mkExistsConst mkLt bound
  where encodeComparison maybeneg quant comp bound var eqs varMap = do 
          varDeclarations <- mapM toApp =<< (liftIO . stToIO $ map snd <$> BC.toList varMap)
          ineq <- comp var =<< mkRealNum bound
          assert =<< maybeneg =<< quant [] varDeclarations =<< mkAnd (ineq:eqs)
        encodeApproxQuery = error "not implemented yet"

computeResult :: TermQuery -> AST -> Z3 TermResult
computeResult ApproxQuery var = fmap (ApproxResult . fromJust . snd) . withModel $ \m -> fromJust <$> evalReal m var
computeResult _ _ = do 
  r <- check
  let cases
        | Sat <- r = return TermSat
        | Unsat <- r = return TermUnsat 
        | Undef <- r = error "Undefined solution error"
  cases
