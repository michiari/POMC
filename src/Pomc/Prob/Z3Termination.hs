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
import Pomc.Prob.SupportGraph

import Data.Hashable(Hashable)

import qualified Data.IntMap.Strict as Map

import Data.Maybe(fromJust, isJust, isNothing)

import Z3.Monad

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad(foldM, unless)
import qualified Control.Monad.ST as ST
import Control.Monad.ST (stToIO, RealWorld)

import qualified Data.Vector.Mutable as MV
import Data.Vector(Vector,(!))
import qualified Data.Vector as V

import Data.Scientific

import qualified Data.HashTable.ST.Basic as BH

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = HashTable RealWorld (Int,Int) AST

--helpers
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

-- (Z3 Var, was it already present?)
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

-- compute the probabilities that a graph will terminate
-- reuires: the initial semiconfiguration is at position 0 in the Support graph
terminationQuery :: (Eq state, Hashable state, Show state)
        => SupportGraph RealWorld state
        -> EncPrecFunc
        -> TermQuery
        -> Z3 TermResult
terminationQuery graph precFun query =
  let encode [] _  = return ()
      encode ((gnId_, rightContext):unencoded) varMap = do
        var <- liftIO . stToIO $ fromJust <$> BH.lookup varMap (gnId_, rightContext)
        gn <- liftIO $ MV.unsafeRead graph gnId_
        let (q,g) = semiconf gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            cases
              -- semiconfigurations with empty stack but not the initial one (terminating semiconfigs -> probability 1)
              | isNothing g && (gnId_ /= 0) = do
                  assert =<< mkEq var =<< mkRealNum (1 :: Prob)
                  return []

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush graph varMap gn rightContext var

              | precRel == Just Equal =
                  encodeShift varMap gn rightContext var

              | precRel == Just Take = do
                  assert =<< mkEq var =<< mkRealNum (Map.findWithDefault 0 rightContext (popContexts gn))
                  return [] -- pop transitions do not generate new variables

              | otherwise = fail "unexpected prec rel"

        new_unencoded <- cases
        encode (new_unencoded ++ unencoded) varMap
  in do
    newVarMap <- liftIO . stToIO $ BH.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO . stToIO $ BH.insert newVarMap (0 :: Int, -1 :: Int) new_var
    -- encode the probability transition relation by asserting a set of Z3 formulas
    encode [(0 ::Int , -1 :: Int)] newVarMap
    solveQuery query new_var graph newVarMap


-- encoding helpers --
encodePush :: (Eq state, Hashable state, Show state)
        => SupportGraph RealWorld state
        -> VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this graph
        -> AST
        -> Z3 [(Int, Int)]
encodePush graph varMap gn rightContext var =
  let closeSummaries pushGn (currs, unencoded_vars) e = do
        supportGn <- liftIO $ MV.unsafeRead graph (to e)
        let varsIds = [(gnId pushGn, getId . fst . semiconf $ supportGn), (gnId supportGn, rightContext)]
        vars <- mapM (lookupVar varMap) varsIds
        eq <- mkMul (map fst vars)
        return (eq:currs,
              [(gnId_, rightContext_) | ((_,alrEncoded), (gnId_, rightContext_)) <- zip vars varsIds, not alrEncoded] ++ unencoded_vars)
      pushEnc (currs, new_vars) e = do
        toGn <- liftIO $ MV.unsafeRead graph (to e)
        (equations, unencoded_vars) <- foldM (closeSummaries toGn) ([], []) (supportEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        return (transition:currs, unencoded_vars ++ new_vars)
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    assert =<< mkEq var =<< mkAdd transitions -- generate the equation for this semiconf
    assert =<< mkGe var =<< mkRational 0
    -- we don't need to assert that var <= 1 because Yannakakis and Etessami didn't report it
    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
        => VarMap
        -> GraphNode state
        -> Int -- the Id of StateId of the right context of this graph
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
    -- we don't need to assert that var <= 1 because Yannakakis and Etessami didn't report it
    return unencoded_vars
-- end 

-- params:
-- (q :: TermQuery) = input query
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph RealWorld state :: ) = the graph 
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveQuery :: TermQuery -> AST -> SupportGraph RealWorld state -> VarMap  -> Z3 TermResult
solveQuery q
  | ApproxAllQuery <- q     = encodeApproxAllQuery
  | ApproxSingleQuery <- q  = encodeApproxSingleQuery
  | PendingQuery <- q       = encodePendingQuery
  | (LT bound) <- q         = encodeComparison mkLt bound
  | (LE bound) <- q         = encodeComparison mkLe bound
  | (GT bound) <- q         = encodeComparison mkLe bound
  | (GE bound) <- q         = encodeComparison mkLt bound
  where encodeComparison comp bound var _ _ = do
          assert =<< comp var =<< mkRealNum bound
          parseResult q <$> check -- check feasibility of all the asserts and interpret the result
        encodeApproxAllQuery _ graph varMap = do 
          vec <- liftIO . stToIO $ groupASTs varMap (MV.length graph)
          sumAstVec <- V.imapM (checkPending graph) vec 
          fmap (ApproxAllResult . fromJust . snd ) . withModel $ \m -> 
            V.forM sumAstVec $ \a -> do 
              s <- astToString . fromJust =<< eval m a
              return $ toRational (read (init s) :: Scientific)
        encodeApproxSingleQuery _ graph varMap = do 
          _ <- parseSMTLib2String "(set-option :pp.decimal true)" [] [] [] []
          _ <- parseSMTLib2String "(set-option :pp.decimal_precision 4)" [] [] [] []
          vec <- liftIO . stToIO $ groupASTs varMap (MV.length graph)
          sumAstVec <- V.imapM (checkPending graph) vec 
          fmap (ApproxSingleResult . fromJust . snd) . withModel $ \m -> do 
            s <- astToString . fromJust =<< eval m (sumAstVec ! 0)
            return (toRational (read (init s) :: Scientific))
        encodePendingQuery _ graph varMap = do 
          vec <- liftIO . stToIO $ groupASTs varMap (MV.length graph)
          PendingResult <$> V.imapM (isPending graph) vec
          
-- Query solving helpers
parseResult :: TermQuery -> Result -> TermResult
parseResult (GE _) Sat   = TermUnsat
parseResult (GE _) Unsat = TermSat 
parseResult (GT _) Sat   = TermUnsat
parseResult (GT _) Unsat = TermSat 
parseResult     _  Sat   = TermSat
parseResult     _  Unsat = TermUnsat 
parseResult     _  Undef = error "Undef result error"

groupASTs :: VarMap -> Int -> ST.ST RealWorld (Vector [AST])
groupASTs varMap l = do
  new_mv <- MV.replicate l []
  BH.mapM_ (\(key, ast) -> MV.unsafeModify new_mv (ast :) (fst key)) varMap
  V.freeze new_mv -- TODO: optimize this as it is linear in the size of the support graph

-- for estimating exact termination probabilities
checkPending :: SupportGraph RealWorld state -> Int -> [AST] -> Z3 AST
checkPending graph i asts = do
  sumAst <- mkAdd asts 
  -- some optimizations for cases where the encoding already contains actual termination probabilities
  -- so there is no need for additional checks
  -- if a semiconf is a pop, then of course it terminates almost surely
  isPop <- liftIO $ not . Map.null . popContexts <$> MV.unsafeRead graph i
  -- if no variable has been encoded for this semiconf, it means it cannot reach any pop (and hence it has zero prob to terminate)
  -- so all the checks down here would be useless (we would be asserting 0 <= 1)
  let noVars = null asts
  -- if a semiconf has bottom stack, then it terminates almost surely 
  -- apart from the initial one, but leaving it out from the encoding does not break uniqueness of solutions
  isBottomStack <- liftIO $ isNothing . snd . semiconf <$> MV.unsafeRead graph i
  unless (isPop || noVars || isBottomStack) $ do
    less1 <- mkLt sumAst =<< mkRealNum (1 :: Prob) -- check if it can be pending
    r <- checkAssumptions [less1]
    let cases 
          | Sat <- r = assert less1 -- semiconf i is pending
          | Unsat <- r = assert =<< mkEq sumAst =<< mkRealNum (1 :: Prob) -- semiconf i is not pending
          | Undef <- r = error $ "Undefined result error when checking pending of semiconf" ++ show i
    cases 
  return sumAst

-- is a semiconf pending?
isPending :: SupportGraph RealWorld state -> Int -> [AST] -> Z3 Bool
isPending graph i asts = do
  sumAst <- mkAdd asts 
  -- some optimizations for cases where we already know if the semiconf is pending
  -- so there is no need for additional checks
  -- if a semiconf is a pop, then of course it terminates almost surely (and hence it is not pending)
  isPop <- liftIO $ not . Map.null . popContexts <$> MV.unsafeRead graph i
  -- if no variable has been encoded for this semiconf, it means it ha zero prob to reach a pop (and hence it is pending)
  let noVars = null asts
  -- if a semiconf has bottom stack, then it belongs necessarily to the support graph
  isBottomStack <- liftIO $ isNothing . snd . semiconf <$> MV.unsafeRead graph i
  if isPop 
    then return False 
    else if noVars || isBottomStack
      then return True
      else do 
        less1 <- mkLt sumAst =<< mkRealNum (1 :: Prob) -- check if it can be pending
        r <- checkAssumptions [less1]
        let cases 
              | Sat <- r = return True -- semiconf i is pending
              | Unsat <- r = return False -- semiconf i is not pending
              | Undef <- r = error $ "Undefined result error when checking pending of semiconf" ++ show i
        cases 
