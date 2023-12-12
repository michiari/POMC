{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                                ) where

import Prelude hiding (LT, GT)

import Pomc.Prec (Prec(..))
import Pomc.Check (EncPrecFunc)

import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, unless, when)
import Control.Monad.ST (RealWorld)

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as Map
import qualified Data.HashTable.IO as HT
import qualified Data.HashMap.Lazy as HM
import Data.Maybe(fromJust, isJust, isNothing)
import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector, (!))
import qualified Data.Vector as V
import Data.Scientific (Scientific)

import Z3.Monad

-- import qualified Debug.Trace as DBG

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = (HT.BasicHashTable VarKey AST, IntSet, Bool)

--helpers
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

-- (Z3 Var, was it already present?)
lookupVar :: VarMap -> EqMap -> VarKey -> Z3 (AST, Bool)
lookupVar (varMap, asPendingIdxs, isASQ) eqMap key = do
  maybeVar <- liftIO $ HT.lookup varMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      new_var <- if IntSet.member (fst key) asPendingIdxs
                      then if snd key == -1 && isASQ
                              then addFixpEq eqMap key (PopEq 1) >> mkRealNum (1 :: Prob)
                              else addFixpEq eqMap key (PopEq 0) >> mkRealNum (0 :: Prob)
                      else mkFreshRealVar $ show key
      liftIO $ HT.insert varMap key new_var
      return (new_var, False)
-- end helpers

-- compute the probabilities that a graph will terminate
-- requires: the initial semiconfiguration is at position 0 in the Support graph
terminationQuery :: (Eq state, Hashable state, Show state)
                 => SupportGraph RealWorld state
                 -> EncPrecFunc
                 -> IntSet -- semiconfs that cannot reach a pop
                 -> TermQuery
                 -> Z3 TermResult
terminationQuery graph precFun asPendingSemiconfs query =
  let mkComp | needEquality query = mkEq
             | otherwise = mkGe
      encode [] _ _ = return ()
      encode ((gnId_, rightContext):unencoded) varMap@(m, _, _) eqMap = do
        let varKey = (gnId_, rightContext)
        var <- liftIO $ fromJust <$> HT.lookup m varKey
        gn <- liftIO $ MV.unsafeRead graph gnId_
        let (q,g) = semiconf gn
            qLabel = getLabel q
            precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
            cases
              | isNothing g && not (IntSet.member gnId_ asPendingSemiconfs) = 
                  error $ "you model is wrong! A semiconf with bottom stack must always reach a SCC: " ++ show (gnId_, rightContext)

              -- this case includes the initial push
              | isNothing g || precRel == Just Yield =
                  encodePush graph varMap eqMap mkComp gn varKey var

              | precRel == Just Equal =
                  encodeShift varMap eqMap mkComp gn varKey var

              | precRel == Just Take = do
                  when (rightContext < 0) $ error $ "Reached a pop with unconsistent left context: " ++ show (gnId_, rightContext)
                  let e = Map.findWithDefault 0 rightContext (popContexts gn)
                  assert =<< mkEq var =<< mkRealNum e
                  addFixpEq eqMap varKey $ PopEq e
                  return [] -- pop transitions do not generate new variables

              | otherwise = fail "unexpected prec rel"

        new_unencoded <- cases
        encode (new_unencoded ++ unencoded) varMap eqMap
  in do
    newMap <- liftIO HT.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO $ HT.insert newMap (0 :: Int, -1 :: Int) new_var
    eqMap <- liftIO HT.new
    -- encode the probability transition relation by asserting a set of Z3 formulas
    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    encode [(0 ::Int , -1 :: Int)] (newMap, asPendingSemiconfs, isApproxSingleQuery query) eqMap
    solveQuery query new_var graph (newMap, asPendingSemiconfs, isApproxSingleQuery query) eqMap


-- encoding helpers --
encodePush :: (Eq state, Hashable state, Show state)
           => SupportGraph RealWorld state
           -> VarMap
           -> EqMap
           -> (AST -> AST -> Z3 AST)
           -> GraphNode state
           -> VarKey
           -> AST
           -> Z3 [(Int, Int)]
encodePush graph varMap@(_, asPendingSemiconfs, approxSingleQuery) eqMap mkComp  gn varKey@(gnId_, rightContext) var  =
  let closeSummaries pushGn (currs, unencoded_vars, terms) e = do
        supportGn <- liftIO $ MV.unsafeRead graph (to e)
        let varsIds = [(gnId pushGn, getId . fst . semiconf $ supportGn), (gnId supportGn, rightContext)]
        vars <- mapM (lookupVar varMap eqMap) varsIds
        eq <- mkMul (map fst vars)
        return ( eq:currs
               , [(gnId__, rightContext_) | ((_,alrEncoded), (gnId__, rightContext_)) <- zip vars varsIds, not alrEncoded] ++ unencoded_vars
               , varsIds:terms
               )
      pushEnc (currs, vars, terms) e = do
        toGn <- liftIO $ MV.unsafeRead graph (to e)
        (equations, unencoded_vars, varTerms) <- foldM (closeSummaries toGn) ([], [], []) (supportEdges gn)
        transition <- encodeTransition e =<< mkAdd equations
        newVars <- if Set.null (supportEdges gn)
                      then do
                        (_, alreadyEncoded) <- lookupVar varMap eqMap (gnId toGn, -2 :: Int)
                        if alreadyEncoded
                          then return []
                          else return [(gnId toGn, -2 :: Int)]
                      else return unencoded_vars
        return ( transition:currs
               , newVars ++ vars
               , (map (\[v1, v2] -> (prob e, v1, v2)) varTerms):terms
               )
  in do
    (transitions, unencoded_vars, terms) <- foldM pushEnc ([], [], []) (internalEdges gn)
    when (not (IntSet.member gnId_ asPendingSemiconfs) || (gnId_ == 0 && approxSingleQuery)) $ do
      assert =<< mkComp var =<< mkAdd transitions -- generate the equation for this semiconf
      assert =<< mkGe var =<< mkRational 0
      addFixpEq eqMap varKey $ PushEq $ concat terms
    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
            => VarMap
            -> EqMap
            -> (AST -> AST -> Z3 AST)
            -> GraphNode state
            -> VarKey
            -> AST
            -> Z3 [(Int, Int)]
encodeShift varMap@(_, asPendingSemiconfs, _) eqMap mkComp gn varKey@(gnId_, rightContext) var =
  let shiftEnc (currs, new_vars, terms) e = do
        let target = (to e, rightContext)
        (toVar, alreadyEncoded) <- lookupVar varMap eqMap target
        trans <- encodeTransition e toVar
        return ( trans:currs
               , if alreadyEncoded then new_vars else target:new_vars
               , (prob e, target):terms
               )
  in do
    (transitions, unencoded_vars, terms) <- foldM shiftEnc ([], [], []) (internalEdges gn)
    unless (IntSet.member gnId_ asPendingSemiconfs) $ do
      assert =<< mkComp var =<< mkAdd transitions -- generate the equation for this semiconf
      assert =<< mkGe var =<< mkRational 0
      addFixpEq eqMap varKey $ ShiftEq terms
    return unencoded_vars
-- end

-- params:
-- (q :: TermQuery) = input query
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph RealWorld state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveQuery :: TermQuery -> AST -> SupportGraph RealWorld state
           -> VarMap -> EqMap -> Z3 TermResult
solveQuery q
  | ApproxAllQuery solv <- q = encodeApproxAllQuery solv
  | ApproxSingleQuery solv <- q = encodeApproxSingleQuery solv
  | PendingQuery solv <- q = encodePendingQuery solv -- TODO: enable hints here and see if it's any better
  | CompQuery comp bound solv <- q = encodeComparison comp bound solv
  where
    encodeApproxAllQuery solv _ graph varMap@(_, asPendingIdxs, _) eqMap = do
      assertHints varMap eqMap solv
      vec <- liftIO $ groupASTs varMap (MV.length graph) (\key -> not (IntSet.member (fst key) asPendingIdxs) || (fst key == 0))
      sumAstVec <- V.imapM (checkPending graph) vec
      setZ3PPOpts
      fmap (ApproxAllResult . fromJust . snd) . withModel $ \m ->
        V.forM sumAstVec $ \a -> do
          s <- astToString . fromJust =<< eval m a
          return $ toRational (read (takeWhile (/= '?') s) :: Scientific)
    encodeApproxSingleQuery solv _ graph varMap@(_, asPendingIdxs, _) eqMap = do
      assertHints varMap eqMap solv
      vec <- liftIO $ groupASTs varMap (MV.length graph) (\key -> not (IntSet.member (fst key) asPendingIdxs) || (fst key == 0))
      sumAstVec <- V.imapM (checkPending graph) vec
      setZ3PPOpts
      fmap (ApproxSingleResult . fromJust . snd) . withModel $ \m -> do
        s <- astToString . fromJust =<< eval m (sumAstVec ! 0)
        return (toRational (read (takeWhile (/= '?') s) :: Scientific))
    encodePendingQuery solv _ graph varMap@(_, asPendingIdxs, _) eqMap = do
      assertHints varMap eqMap solv
      vec <- liftIO $ groupASTs varMap (MV.length graph) (\key -> not (IntSet.member (fst key) asPendingIdxs))
      PendingResult <$> V.imapM (isPending graph) vec

    assertHints varMap eqMap solver = case solver of
      SMTWithHints -> doAssert defaultTolerance
      SMTCert eps -> doAssert eps
      _ -> return ()
      where doAssert eps = do
              let iterEps = min defaultEps $ eps * eps
              approxVec <- approxFixp eqMap iterEps defaultMaxIters
              approxFracVec <- toRationalProbVec iterEps approxVec
              epsReal <- mkRealNum eps
              mapM_ (\(varKey, p) -> do
                        (var, True) <- lookupVar varMap eqMap varKey
                        pReal <- mkRealNum p
                        assert =<< mkGe var pReal
                        assert =<< mkLe var =<< mkAdd [pReal, epsReal]
                    ) approxFracVec

    setZ3PPOpts = do
      _ <- parseSMTLib2String "(set-option :pp.decimal true)" [] [] [] []
      _ <- parseSMTLib2String "(set-option :pp.decimal_precision 10)" [] [] [] []
      return ()

    encodeComparison comp bound solver var _ varMap eqMap = do
      assertHints varMap eqMap solver
      let mkComp = case comp of
            Lt -> mkLt
            Le -> mkLe
            Gt -> mkLe
            Ge -> mkLt
      assert =<< mkComp var =<< mkRealNum bound
      -- check feasibility of all the asserts and interpret the result
      parseResult comp <$> check
        where parseResult :: Comp -> Result -> TermResult
              parseResult Ge Sat   = TermUnsat
              parseResult Ge Unsat = TermSat
              parseResult Gt Sat   = TermUnsat
              parseResult Gt Unsat = TermSat
              parseResult _  Sat   = TermSat
              parseResult _  Unsat = TermUnsat
              parseResult _  Undef = error "Undef result error"


-- Query solving helpers
groupASTs :: VarMap -> Int -> ((Int, Int) -> Bool) -> IO (Vector [AST])
groupASTs (varMap, _, _) len cond = do
  new_mv <- MV.replicate len []
  HT.mapM_ (\(key, ast) -> when (cond key) $ MV.unsafeModify new_mv (ast :) (fst key)) varMap
  V.freeze new_mv -- TODO: optimize this as it is linear in the size of the support graph

-- for estimating exact termination probabilities
checkPending :: SupportGraph RealWorld state -> Int -> [AST] -> Z3 AST
checkPending graph idx asts = do
  sumAst <- mkAdd asts
  -- some optimizations for cases where the encoding already contains actual termination probabilities
  -- so there is no need for additional checks
  -- if a semiconf is a pop, then of course it terminates almost surely
  isPop <- liftIO $ not . Map.null . popContexts <$> MV.unsafeRead graph idx
  -- if no variable has been encoded for this semiconf, it means it cannot reach any pop (and hence it has zero prob to terminate)
  -- so all the checks down here would be useless (we would be asserting 0 <= 1)
  let noVars = null asts
  unless (isPop || noVars) $ do
    less1 <- mkLt sumAst =<< mkRealNum (1 :: Prob) -- check if it can be pending
    r <- checkAssumptions [less1]
    let cases
          | Sat <- r = assert less1 -- semiconf i is pending
          | Unsat <- r = assert =<< mkEq sumAst =<< mkRealNum (1 :: Prob) -- semiconf i is not pending
          | Undef <- r = error $ "Undefined result error when checking pending of semiconf" ++ show idx
    cases
  return sumAst

-- is a semiconf pending?
isPending :: SupportGraph RealWorld state -> Int -> [AST] -> Z3 Bool
isPending graph idx asts = do
  sumAst <- mkAdd asts
  -- some optimizations for cases where we already know if the semiconf is pending
  -- so there is no need for additional checks
  -- if a semiconf is a pop, then of course it terminates almost surely (and hence it is not pending)
  isPop <- liftIO $ not . Map.null . popContexts <$> MV.unsafeRead graph idx
  -- if no variable has been encoded for this semiconf, it means it ha zero prob to reach a pop (and hence it is pending)
  let noVars = null asts
  if isPop
    then return False
    else if noVars
            then return True
            else do
              less1 <- mkLt sumAst =<< mkRealNum (1 :: Prob) -- check if it can be pending
              eq <- mkEq sumAst =<< mkRealNum (1 :: Prob)
              r <- checkAssumptions [less1]
              let cases
                    | Sat <- r = assert less1 >> return True
                    | Unsat <- r = assert eq >> return False -- semiconf i is not pending
                    | Undef <- r = error $ "Undefined result error when checking pending of semiconf" ++ show idx
              cases
