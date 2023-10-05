{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                                ) where

import Prelude hiding (LT, GT)

import Pomc.Prec (Prec(..),)
import Pomc.Check (EncPrecFunc)

import Pomc.Prob.ProbUtils
import Pomc.Prob.SummaryChain

import Data.Hashable(Hashable)

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

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
        -> Z3 TermResult
terminationQuery chain precFun query =
  let encode [] _  pops = return pops
      encode ((gnId_, rightContext):unencoded) varMap pops = do
        var <- liftIO . stToIO $ fromJust <$> BH.lookup varMap (gnId_, rightContext)
        gn <- liftIO $ MV.unsafeRead chain gnId_
        let (q,g) = node gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            --update the set of pop semiconfs, if needed
            recordPop = isApprox query && isJust g && precRel == Just Take 
            new_pops = if recordPop then IntSet.insert gnId_ pops else pops
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

              | precRel == Just Take = do
                  assert =<< mkEq var =<< mkRealNum (Map.findWithDefault 0 rightContext (popContexts gn))
                  return [] -- pop transitions do not generate new variables

              | otherwise = fail "unexpected prec rel"

        new_unencoded <- cases
        encode (new_unencoded ++ unencoded) varMap new_pops
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var
    pops <- encode [(0 ::Int , -1 :: Int)] newVarMap IntSet.empty -- encode the probability transition relation via a set of Z3 formulas represented via ASTs
    solveQuery query new_var pops chain newVarMap

encodePush :: (Eq state, Hashable state, Show state)
        => SummaryChain RealWorld state
        -> VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 [(Int, Int)]
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
    assert =<< mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    assert =<< mkGe var =<< mkRational 0
    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this chain
        -> AST
        -> Z3 [(Int, Int)]
encodeShift varMap gn rightContext var =
  let shiftEnc (currs, new_vars) e = do
        (toVar, alreadyEncoded) <- lookupVar varMap (to e, rightContext)
        trans <- encodeTransition e toVar
        return (trans:currs, if alreadyEncoded then new_vars else (to e, rightContext):new_vars)
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    assert =<< mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    assert =<< mkGe var =<< mkRational 0
    return unencoded_vars

solveQuery :: TermQuery -> AST -> IntSet -> SummaryChain RealWorld state -> VarMap  -> Z3 TermResult
solveQuery q
  | ApproxQuery <- q = encodeApproxQuery
  | (LT bound) <- q  = encodeComparison mkLt bound
  | (LE bound) <- q  = encodeComparison mkLe bound
  | (GT bound) <- q  = encodeComparison mkLe bound
  | (GE bound) <- q  = encodeComparison mkLt bound
  where encodeComparison comp bound var _ _ _ = do
          assert =<< comp var =<< mkRealNum bound
          parseResult q <$> check
        encodeApproxQuery _ pops chain varMap = do 
          vec <- liftIO . stToIO $ groupASTs varMap (MV.length chain)
          sumAstVec <- V.imapM (checkDeficiency pops) vec 
          fmap (ApproxResult . fromJust . snd) . withModel $ \m -> fromJust <$> mapEval evalReal m sumAstVec
          
-- Query solving helpers
parseResult :: TermQuery -> Result -> TermResult
parseResult (GE _) Sat   = TermUnsat
parseResult (GE _) Unsat = TermSat 
parseResult (GT _) Sat   = TermUnsat
parseResult (GT _) Unsat = TermSat 
parseResult     _  Sat   = TermSat
parseResult     _  Unsat = TermUnsat 
parseResult     _  Undef = error "Undef result error"

groupASTs :: VarMap -> Int -> ST.ST RealWorld (V.Vector [AST])
groupASTs varMap l = do
  new_mv <- MV.replicate l []
  BH.mapM_ (\(key, ast) -> MV.unsafeModify new_mv (ast :) (fst key)) varMap
  V.freeze new_mv

checkDeficiency :: IntSet -> Int -> [AST] -> Z3 AST
checkDeficiency pops i asts = do
  sumAst <- mkAdd asts 
  unless (IntSet.member i pops) $ do -- pop semiconfs do not need additional constraints
    less1 <- mkLt sumAst =<< mkRational (1 :: Prob)
    r <- checkAssumptions [less1]
    let cases 
          | Sat <- r = assert less1 
          | Unsat <- r = assert =<< mkEq sumAst =<< mkRational (1 :: Prob) -- semiconf i is not deficient
          | Undef <- r = error $ "Undefined result error when checking deficiency of node" ++ show i
    cases 
  return sumAst
