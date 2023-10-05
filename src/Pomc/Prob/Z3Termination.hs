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

import Data.Set(Set)
import qualified Data.Set as Set

import qualified Data.IntMap.Strict as Map

import Data.Maybe(fromJust, isJust, isNothing)

import Z3.Monad

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad(foldM, unless)
import qualified Control.Monad.ST as ST
import Control.Monad.ST (stToIO, RealWorld)

import qualified Data.Vector.Mutable as MV

import qualified Data.Vector as V

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
  let encode [] _  eqs pops = return (eqs, pops)
      encode ((gnId_, rightContext):unencoded) varMap eqs pops = do
        var <- liftIO . stToIO $ fromJust <$> BH.lookup varMap (gnId_, rightContext)
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            recordPop = isJust g && precRel == Just Take && isApprox query
            new_pops = if recordPop then Set.insert gnId_ pops else pops
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating states -> probability 1)
              | isNothing g && (gnId_ /= 0) = do
                  equation <- mkEq var =<< mkRealNum (1 :: Prob)
                  return ([], [equation])

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush chain varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take = do
                    equation <- mkEq var =<< mkRealNum (Map.findWithDefault 0 rightContext (popContexts gn))
                    return ([], [equation]) -- pop transitions do not generate new variables

              | otherwise = fail "unexpected prec rel"

        (new_unencoded, new_eqs) <- cases
        encode (new_unencoded ++ unencoded) varMap (new_eqs ++ eqs) new_pops
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var
    (equations, pops) <- encode [(0 ::Int , -1 :: Int)] newVarMap [] Set.empty -- encode the probability transition relation via a set of Z3 formulas represented via ASTs

    -- a string representation of the SMT Encoding for debugging purposes
    debugMsg <- foldM (\acc eq -> do
      eqString <- astToString eq
      return (acc ++ eqString ++ "\n")
      )
      ""
      equations
    termRes <- encodeQuery query new_var equations pops chain newVarMap
    return (termRes, debugMsg)

encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], [AST])
encodePush chain varMap gn rightContext var =
  let closeSummaries pushGn (currs, unencoded_vars) e = do
        summaryGn <- liftIO $ MV.unsafeRead chain (to e)
        let varsIds = [(gnId pushGn, getId . fst . node $ summaryGn), (gnId summaryGn, rightContext)]
        vars <- mapM (lookupVar varMap) varsIds
        eq <- mkMul (map fst vars)
        return (eq:currs,
              [(gnId_, rightContext_) | ((_,alrEncoded), (gnId_, rightContext_)) <- zip vars varsIds, not alrEncoded] ++ unencoded_vars)
      pushEnc (currs, new_vars) e = do
        toGn <- liftIO $ MV.unsafeRead chain (to e)
        (equations, unencoded_vars) <- foldM (closeSummaries toGn) ([], []) (summaryEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        return (transition:currs, unencoded_vars ++ new_vars)
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    geZero <- mkGe var =<< mkRational 0
    return (unencoded_vars, [equation, geZero])

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 ([(Int, Int)], [AST])
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (toVar, alreadyEncoded) <- lookupVar varMap (to e, rightContext)
        trans <- encodeTransition e toVar
        return (trans:currs, if alreadyEncoded then new_vars else (to e, rightContext):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    equation <- mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    geZero <- mkGe var =<< mkRational 0
    return (unencoded_vars, [equation, geZero])

encodeQuery :: TermQuery -> AST -> [AST] -> Set Int -> SummaryChain RealWorld state -> VarMap  -> Z3 TermResult
encodeQuery q
  | ApproxQuery <- q = encodeApproxQuery
  | (LT bound) <- q  = encodeComparison return mkExistsConst mkLt bound
  | (LE bound) <- q  = encodeComparison return mkExistsConst mkLe bound
  | (GT bound) <- q  = encodeComparison mkNot  mkExistsConst mkLe bound
  | (GE bound) <- q  = encodeComparison mkNot  mkExistsConst mkLt bound
  where encodeComparison maybeneg quant comp bound var eqs _ _ varMap = do
          varDeclarations <- mapM toApp =<< (liftIO . stToIO $ map snd <$> BC.toList varMap)
          ineq <- comp var =<< mkRealNum bound
          assert =<< maybeneg =<< quant [] varDeclarations =<< mkAnd (ineq:eqs)
          computeResult q V.empty
        encodeApproxQuery _ eqs pops chain varMap = do 
          assert =<< mkAnd eqs
          vec <- liftIO . stToIO $ freezeVector varMap (MV.length chain)
          sumAstVec <- V.imapM (checkDeficiency pops) vec 
          computeResult q sumAstVec
          
-- helpers
checkDeficiency :: Set Int -> Int -> [AST] -> Z3 AST
checkDeficiency pops i asts = do
  sumAst <- mkAdd asts 
  unless (Set.member i pops) $ do 
    less1 <- mkLt sumAst =<< mkRational (1 :: Prob)
    equal1 <- mkEq sumAst =<< mkRational (1 :: Prob)
    r <- checkAssumptions [less1]
    let cases 
          | Sat <- r = assert less1 
          | Unsat <- r = assert equal1
          | Undef <- r = error $ "Undefined solution error when checking deficiency of node" ++ show i
    cases 
  return sumAst

freezeVector :: VarMap -> Int -> ST.ST RealWorld (V.Vector [AST])
freezeVector varMap l = do
  new_mv <- MV.replicate l []
  BH.mapM_ (\(key, ast) -> MV.unsafeModify new_mv (ast :) (fst key)) varMap
  V.freeze new_mv

computeResult :: TermQuery -> V.Vector AST -> Z3 TermResult
computeResult ApproxQuery vars = fmap (ApproxResult . fromJust . snd) . withModel $ \m -> fromJust <$> mapEval evalReal m vars
computeResult _ _ = do
  r <- check
  let cases
        | Sat <- r = return TermSat
        | Unsat <- r = return TermUnsat
        | Undef <- r = error "Undefined solution error"
  cases
