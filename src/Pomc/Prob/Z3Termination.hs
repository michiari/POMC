{-# LANGUAGE LambdaCase #-}
{- |
   Module      : Pomc.Prob.Z3Termination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Z3Termination ( terminationQuery
                               , terminationQuerySCC
                               ) where

import Prelude hiding (LT, GT)

import Pomc.Prec (Prec(..))
import Pomc.Check (EncPrecFunc)

import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as ZS

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, unless, when, forM_, forM)
import Control.Monad.ST (RealWorld)

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as Map

import qualified Data.Map as GeneralMap
import qualified Data.HashTable.IO as HT
import qualified Data.HashMap.Lazy as HM
import Data.Maybe(fromJust, isJust, isNothing)
import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector, (!))
import qualified Data.Vector as V
import Data.Scientific (Scientific)
import Data.Ratio (approxRational)


import Z3.Monad
import Data.IORef (IORef, newIORef, modifyIORef, readIORef, writeIORef)

import qualified Debug.Trace as DBG
import Data.List (nub, groupBy)

-- a map Key: (gnId GraphNode, getId StateId) - value : Z3 variables (represented as ASTs)
-- each Z3 variable represents [[q,b | p ]]
-- where q,b is the semiconfiguration associated with the graphNode of the key
-- and p is the state associated with the StateId of the key
type VarMap = (HT.BasicHashTable VarKey AST, HT.BasicHashTable VarKey AST, IntSet, Bool)

--helpers
encodeTransition :: Edge -> AST -> Z3 AST
encodeTransition e toAST = do
  probReal <- mkRealNum (prob e)
  mkMul [probReal, toAST]

-- (Z3 Var, was it already present?)
lookupVar :: VarMap -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType) -> VarKey -> Z3 (AST, Bool)
lookupVar (varMap, newAdded, asPendingIdxes, encodeInitial) (lEqMap, uEqMap) key = do
  maybeVar <- liftIO $ HT.lookup varMap key
  if isJust maybeVar
    then do
      return (fromJust maybeVar, True)
    else do
      new_var <- if IntSet.member (fst key) asPendingIdxes
                  then if snd key == -1 && encodeInitial
                    then addFixpEq lEqMap key (PopEq 1) >> addFixpEq uEqMap key (PopEq 1) >> mkRealNum (1 :: EqMapNumbersType)
                    else addFixpEq lEqMap key (PopEq 0) >> addFixpEq uEqMap key (PopEq 0) >> mkRealNum (0 :: EqMapNumbersType)
                  else do
                    var <- mkFreshRealVar $ show key
                    liftIO $ HT.insert newAdded key var
                    return var
      liftIO $ HT.insert varMap key new_var
      return (new_var, False)
-- end helpers

-- compute the probabilities that a graph will terminate
-- requires: the initial semiconfiguration is at position 0 in the Support graph
terminationQuery :: (Eq state, Hashable state, Show state)
                 => SupportGraph RealWorld state
                 -> EncPrecFunc
                 -> (IntSet, IntSet) -- semiconfs that cannot reach a pop, and a subset of those that do it almost surely
                 -> TermQuery
                 -> Z3 TermResult
terminationQuery graph precFun (asPending, asNonPending) query = do
    newMap <- liftIO HT.new
    unusedMap <- liftIO HT.new
    new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
    liftIO $ HT.insert newMap (0 :: Int, -1 :: Int) new_var
    lowerEqMap <- liftIO HT.new
    upperEqMap <- liftIO HT.new
    -- encode the probability transition relation by asserting a set of Z3 formulas
    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    encode [(0 ::Int , -1 :: Int)] (newMap, unusedMap, asPending, encodeInitialSemiconf query) (lowerEqMap, upperEqMap) graph precFun mkGe query
    error "fix it according to recent lower and upper EqMap"
    --solveQuery query new_var graph (newMap, unusedMap, asPending, encodeInitialSemiconf query) asNonPending eqMap


encode :: (Eq state, Hashable state, Show state)
      => [(Int, Int)]
      -> VarMap
      -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
      -> SupportGraph RealWorld state
      -> EncPrecFunc
      -> (AST -> AST -> Z3 AST)
      -> TermQuery
      -> Z3 ()
encode [] _ _ _ _ _ _ = return ()
encode ((gnId_, rightContext):unencoded) varMap@(m, _,  asPendingIdxes, _) (lowerEqMap, upperEqMap) graph precFun mkComp query = do
  let varKey = (gnId_, rightContext)
  --DBG.traceM $ "Encoding variable for: " ++ show (gnId_, rightContext)
  --DBG.traceM $ "Almost surely pending semiconfs: " ++ show asPendingSemiconfs
  var <- liftIO $ fromJust <$> HT.lookup m varKey
  gn <- liftIO $ MV.unsafeRead graph gnId_
  let (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        | isNothing g && not (IntSet.member gnId_ asPendingIdxes) =
            error $ "you model is wrong! A semiconf with bottom stack must almost surely reach a SCC: " ++ show (gnId_, rightContext)

        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush graph varMap (lowerEqMap, upperEqMap) mkComp gn varKey var

        | precRel == Just Equal =
            encodeShift varMap (lowerEqMap, upperEqMap) mkComp gn varKey var

        | precRel == Just Take = do
            when (rightContext < 0) $ error $ "Reached a pop with unconsistent left context: " ++ show (gnId_, rightContext)
            let e = Map.findWithDefault 0 rightContext (popContexts gn)
            eq <- mkEq var =<< mkRealNum e
            --eqString <- astToString eq
            --DBG.traceM $ "Asserting Pop equation: " ++ eqString
            --assert eq
            addFixpEq lowerEqMap varKey $ PopEq $ fromRational e
            addFixpEq upperEqMap varKey $ PopEq $ fromRational e
            return [] -- pop transitions do not generate new variables

        | otherwise = fail "unexpected prec rel"

  new_unencoded <- cases
  encode (new_unencoded ++ unencoded) varMap (lowerEqMap, upperEqMap) graph precFun mkComp query

-- encoding helpers --
encodePush :: (Eq state, Hashable state, Show state)
           => SupportGraph RealWorld state
           -> VarMap
           -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
           -> (AST -> AST -> Z3 AST)
           -> GraphNode state
           -> VarKey
           -> AST
           -> Z3 [(Int, Int)]
encodePush graph varMap@(_, _, asPendingIdxes, approxSingleQuery) (lowerEqMap, upperEqMap) mkComp  gn varKey@(gnId_, rightContext) var  =
  let closeSummaries pushGn (currs, unencoded_vars, terms) e = do
        supportGn <- liftIO $ MV.unsafeRead graph (to e)
        let varsIds = [(gnId pushGn, getId . fst . semiconf $ supportGn), (gnId supportGn, rightContext)]

        vars <- mapM (lookupVar varMap (lowerEqMap, upperEqMap)) varsIds
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
                        (_, alreadyEncoded) <- lookupVar varMap (lowerEqMap, upperEqMap) (gnId toGn, -2 :: Int)
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
    when (not (IntSet.member gnId_ asPendingIdxes) || (gnId_ == 0 && approxSingleQuery)) $ do
      eq <- mkComp var =<< mkAdd transitions -- generate the equation for this semiconf
      --eqString <- astToString eq
      --DBG.traceM $ "Asserting Push equation: " ++ eqString
      --assert eq
      --assert =<< mkGe var =<< mkRealNum 0
      addFixpEq upperEqMap varKey $ PushEq $ concat terms
      addFixpEq lowerEqMap varKey $ PushEq $ concat terms

    return unencoded_vars

encodeShift :: (Eq state, Hashable state, Show state)
            => VarMap
            -> (EqMap EqMapNumbersType, EqMap EqMapNumbersType)
            -> (AST -> AST -> Z3 AST)
            -> GraphNode state
            -> VarKey
            -> AST
            -> Z3 [(Int, Int)]
encodeShift varMap@(_, _, asPendingIdxes, _) (lowerEqMap, upperEqMap) mkComp gn varKey@(gnId_, rightContext) var =
  let shiftEnc (currs, new_vars, terms) e = do
        let target = (to e, rightContext)
        (toVar, alreadyEncoded) <- lookupVar varMap(lowerEqMap, upperEqMap) target
        trans <- encodeTransition e toVar
        return ( trans:currs
               , if alreadyEncoded then new_vars else target:new_vars
               , (prob e, target):terms
               )
  in do
    (transitions, unencoded_vars, terms) <- foldM shiftEnc ([], [], []) (internalEdges gn)
    unless (IntSet.member gnId_ asPendingIdxes) $ do
      eq <- mkComp var =<< mkAdd transitions -- generate the equation for this semiconf
      --eqString <- astToString eq
      --DBG.traceM $ "Asserting Shift equation: " ++ eqString
      --assert eq
      --assert =<< mkGe var =<< mkRealNum 0
      addFixpEq lowerEqMap varKey $ ShiftEq terms
      addFixpEq lowerEqMap varKey $ ShiftEq terms
    return unencoded_vars
-- end

-- params:
-- (q :: TermQuery) = input query
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph RealWorld state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveQuery :: TermQuery -> AST -> SupportGraph RealWorld state
           -> VarMap -> IntSet -> EqMap EqMapNumbersType -> Z3 TermResult
solveQuery q
  | ApproxAllQuery solv <- q = encodeApproxAllQuery (getTolerance solv)
  | ApproxSingleQuery solv <- q = encodeApproxSingleQuery (getTolerance solv)
  | PendingQuery solv <- q = encodePendingQuery (getTolerance solv)-- TODO: enable hints here and see if it's any better
  | CompQuery comp bound solv <- q = encodeComparison comp bound solv
  where
    encodeApproxAllQuery eps _ graph varMap@(m, _, asPendingIdxs, _) _ eqMap = do
      assertHints varMap eqMap eps
      upperBoundModel <- fromJust . snd <$> getModel
      filteredASTs <- filter (\(key, _) -> not (IntSet.member (fst key) asPendingIdxs)) <$> liftIO (HT.toList m)
      setZ3PPOpts
      ub <-  GeneralMap.fromList <$> forM filteredASTs (\(varKey, var) -> do
                s <- astToString . fromJust =<< eval upperBoundModel var
                return (varKey, toRational (read (takeWhile (/= '?') s) :: Scientific)))
                
      lbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, approxRational (d - eps) eps)) <$> liftIO (HT.toList eqMap)
      return $ ApproxAllResult (lbMap, ub)
    encodeApproxSingleQuery eps _ _ varMap@(m, _, _, _) _ eqMap = do
      assertHints varMap eqMap eps
      upperBoundModel <- fromJust . snd <$> getModel
      setZ3PPOpts
      ub <- astToString . fromJust =<< eval upperBoundModel . fromJust =<< liftIO (HT.lookup m (0,-1))
      lb <- (\(PopEq d) -> approxRational (d - eps) eps) . fromJust <$> liftIO (HT.lookup eqMap (0,-1))
      return $ ApproxSingleResult (lb, toRational (read (takeWhile (/= '?') ub) :: Scientific))

    encodePendingQuery solv _ graph varMap@(m, _, asPendingIdxs, _) asNonPendingIdxs eqMap = do
      DBG.traceM "Asserting hints"
      assertHints varMap eqMap solv
      DBG.traceM "Computing an overrapproximating model"
      model <- fromJust . snd <$> getModel
      vec <- liftIO $ groupASTs m (MV.length graph) (\key -> not (IntSet.member (fst key) asPendingIdxs))
      PendingResult <$> V.imapM (isPending graph model asNonPendingIdxs) vec

    getTolerance SMTWithHints = defaultTolerance
    getTolerance (SMTCert eps) = eps
    getTolerance _ = error "You must use hints in the current version!!"

    getMaybeTolerance SMTWithHints = Just defaultTolerance
    getMaybeTolerance (SMTCert eps) = Just eps
    getMaybeTolerance _ = Nothing

    assertHints varMap eqMap  eps = do
      -- oviRes <- ovi defaultOVISettingsDouble eqMap
      -- oviToRational defaultOVISettingsDouble eqMap oviRes
      -- oviveclist <- liftIO $ HT.toList $ oviUpperBound oviRes
      -- DBG.traceM $ "OVI result: " ++ show (oviSuccess oviRes) ++ show oviveclist
      let iterEps = min defaultEps $ eps * eps
      -- DBG.traceShowM =<< (liftIO $ HT.toList eqMap)
      approxVec <- approxFixp eqMap iterEps defaultMaxIters
      -- DBG.traceShowM =<< (liftIO $ HT.toList approxVec)
      approxFracVec <- toRationalProbVec iterEps approxVec
      DBG.traceM "Computed a lower bound!"
      enlargeBounds approxFracVec eps
      -- updating with found values
      forM_  approxFracVec $ \(varKey, _, p) -> do
        liftIO (HT.lookup eqMap varKey) >>= \case
          Just (PopEq _) -> return () -- An eq constraint has already been asserted
          _ -> addFixpEq eqMap varKey (PopEq p)
      where enlargeBounds approxFracVec eps = do
              epsReal <- mkRealNum eps
              bounds <- concat <$> forM approxFracVec (\(varKey, pRational, _) -> liftIO (HT.lookup eqMap varKey) >>= \case
                Just (PopEq _) -> return [] -- An eq constraint has already been asserted
                _ -> do
                  (var, True) <- lookupVar varMap (eqMap, error "refactor for uEqMap") varKey
                  pReal <- mkRealNum pRational
                  lb <- mkGe var pReal
                  ub <-  mkLe var =<< mkAdd [pReal, epsReal]
                  return [lb, ub])
              --DBG.traceM "Collected some requirements"
              checkAssumptions bounds >>= \case
                  Sat -> mapM_ assert bounds
                  Unsat -> enlargeBounds approxFracVec (2 * eps)
                  Undef -> error "undefinite result when checking an SCC"

    setZ3PPOpts = do
      _ <- parseSMTLib2String "(set-option :pp.decimal true)" [] [] [] []
      _ <- parseSMTLib2String "(set-option :pp.decimal_precision 10)" [] [] [] []
      return ()

    encodeComparison comp bound solver var _ varMap _ eqMap = do
      --DBG.traceM $ "encoding comparison! " ++ show comp ++ " " ++ show bound
      when (isJust $ getMaybeTolerance solver) $ DBG.trace "asserting Hints" $ assertHints varMap eqMap (getTolerance solver)
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
groupASTs :: HT.BasicHashTable VarKey AST -> Int -> ((Int, Int) -> Bool) -> IO (Vector [AST])
groupASTs varMap len cond = do
  new_mv <- MV.replicate len []
  HT.mapM_ (\(key, ast) -> when (cond key) $ MV.unsafeModify new_mv (ast :) (fst key)) varMap
  V.freeze new_mv -- TODO: optimize this as it is linear in the size of the support graph

-- is a semiconf pending?
isPending :: SupportGraph RealWorld state -> Model -> IntSet -> Int -> [AST] -> Z3 Bool
isPending graph m asNonPendingIdxs idx asts = do
  sumAst <- mkAdd asts
  -- some optimizations for cases where we already know if the semiconf is pending
  -- so there is no need for additional checks
  -- if a semiconf is a pop, then of course it terminates almost surely (and hence it is not pending)
  isPop <- liftIO $ not . Map.null . popContexts <$> MV.unsafeRead graph idx
  -- if no variable has been encoded for this semiconf, it means it ha zero prob to reach a pop (and hence it is pending)
  let noVars = null asts
      asNonPending = IntSet.member idx asNonPendingIdxs
  less1 <- mkLt sumAst =<< mkRealNum (1 :: Prob) -- check if it can be pending
  isUpperBounded <- fromJust <$> (evalBool m =<< mkLt sumAst =<< mkRealNum (1 :: Prob))
  eq <- mkEq sumAst =<< mkRealNum (1 :: Prob)
  if isPop || asNonPending
    then return False
    else if noVars || isUpperBounded
            then return True
            else do
              r <- checkAssumptions [less1]
              let cases
                    | Sat <- r = assert less1 >> return True
                    | Unsat <- r = assert eq >> return False -- semiconf i is not pending
                    | Undef <- r = error $ "Undefined result error when checking pending of semiconf" ++ show idx
              cases

---------------------------------------------------------------------------------------------------
-- compute the exact termination probabilities, but do it with a backward analysis for every SCC --
---------------------------------------------------------------------------------------------------

type SuccessorsPopContexts = IntSet

type PartialVarMap = (HT.BasicHashTable VarKey AST, Bool)

data DeficientGlobals state = DeficientGlobals
  { supportGraph :: SupportGraph RealWorld state
  , sStack     :: IOStack Int
  , bStack     :: IOStack Int
  , iVector    :: MV.IOVector Int
  , successorsCntxs :: MV.IOVector SuccessorsPopContexts
  , mustReachPop :: IORef IntSet
  , cannotReachPop :: IORef IntSet
  , partialVarMap :: PartialVarMap
  , rewVarMap :: RewVarMap
  , upperEqMap :: EqMap EqMapNumbersType
  , lowerEqMap :: EqMap EqMapNumbersType
  , eps :: IORef EqMapNumbersType
  }


-- requires: the initial semiconfiguration is at position 0 in the Support graph
terminationQuerySCC :: (Eq state, Hashable state, Show state)
                 => SupportGraph RealWorld state
                 -> EncPrecFunc
                 -> TermQuery
                 -> Z3 (TermResult, IntSet)
terminationQuerySCC suppGraph precFun query = do
  newSS              <- liftIO ZS.new
  newBS              <- liftIO ZS.new
  newIVec            <- liftIO $ MV.replicate (MV.length suppGraph) 0
  newSuccessorsCntxs <- liftIO $ MV.replicate (MV.length suppGraph) IntSet.empty
  emptyCannotReachPop <- liftIO $ newIORef IntSet.empty
  newMap <- liftIO HT.new
  newUpperEqMap <- liftIO HT.new
  newLowerEqMap <- liftIO HT.new
  emptyMustReachPop <- liftIO $ newIORef IntSet.empty
  newRewVarMap <- liftIO HT.new
  newEps <- case (solver query) of
              SMTWithHints -> liftIO $ newIORef defaultTolerance
              SMTCert givenEps -> liftIO $ newIORef givenEps
              _ -> error "you cannot use pure SMT when computing termination SCC-based"
  let globals = DeficientGlobals { supportGraph = suppGraph
                                , sStack = newSS
                                , bStack = newBS
                                , iVector = newIVec
                                , successorsCntxs = newSuccessorsCntxs
                                , mustReachPop = emptyMustReachPop
                                , cannotReachPop = emptyCannotReachPop
                                , partialVarMap = (newMap, encodeInitialSemiconf query)
                                , rewVarMap = newRewVarMap
                                , upperEqMap = newUpperEqMap
                                , lowerEqMap = newLowerEqMap
                                , eps = newEps
                                }
  -- passing some parameters
  setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
  _ <- parseSMTLib2String "(set-option :pp.decimal true)" [] [] [] []
  _ <- parseSMTLib2String "(set-option :pp.decimal_precision 5)" [] [] [] []
  -- perform the Gabow algorithm to determine semiconfs that cannot reach a pop
  gn <- liftIO $ MV.unsafeRead suppGraph 0
  addtoPath globals gn
  _ <- dfs globals precFun query gn
  -- returning the computed values
  currentEps <- liftIO $ readIORef (eps globals)
  mustReachPopIdxs <- liftIO $ readIORef (mustReachPop globals)
  let actualEps = min defaultEps $ currentEps * currentEps
      readResults
        | ApproxAllQuery _ <- query = readApproxAllQuery
        | ApproxSingleQuery _ <- query = readApproxSingleQuery
        | otherwise = error "cannot use SCC decomposition for queries that do not estimate the actual probabilities"
        where
          readApproxAllQuery = do
            
            {- I keep this thing for reference, we will need it to compare with the Z3-based approach
            groupedVec <- liftIO $ groupASTs newMap  (MV.length suppGraph) (\key -> not (IntSet.member (fst key) asPendingIdxs))
            sumAstVec <- V.mapM mkAdd groupedVec
            ub <-  V.forM sumAstVec $ \a -> do
                sumVar <-  reset >> mkFreshRealVar "dummy"
                m <-  mkEq sumVar a >>= assert >> fromJust . snd <$> getModel
                s <- astToString . fromJust =<< eval m sumVar
                return $ toRational (read (takeWhile (/= '?') s) :: Scientific)
            -}
            upperProbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, d)) <$> liftIO (HT.toList newUpperEqMap)
            let upperProbRationalMap = GeneralMap.map (\v -> approxRational (v + actualEps) actualEps) upperProbMap
            lowerProbMap <- GeneralMap.fromList . map (\(k, PopEq d) -> (k, d)) <$> liftIO (HT.toList newLowerEqMap)
            let lowerProbRationalMap = GeneralMap.map (\v -> approxRational (v - actualEps) actualEps) lowerProbMap
            return  (ApproxAllResult (lowerProbRationalMap, upperProbRationalMap), mustReachPopIdxs)
          readApproxSingleQuery = do
              {-
              ub <- astToString . fromJust =<< liftIO (HT.lookup newMap (0,-1))
              toRational (read (takeWhile (/= '?') ub :: Scientific))
              -}
              ub <- (\(PopEq d) -> approxRational (d + actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newUpperEqMap (0,-1))
              lb <- (\(PopEq d) -> approxRational (d - actualEps) actualEps) . fromJust <$> liftIO (HT.lookup newLowerEqMap (0,-1))

              return (ApproxSingleResult (lb, ub) , mustReachPopIdxs)
  readResults

dfs :: (Eq state, Hashable state, Show state)
    => DeficientGlobals state
    -> EncPrecFunc
    -> TermQuery
    -> GraphNode state
    -> Z3 (SuccessorsPopContexts, Bool)
dfs globals precFun query gn =
  let cases nextNode iVal
        | (iVal == 0) = addtoPath globals nextNode >> dfs globals precFun query nextNode
        | (iVal < 0)  = liftIO $ do
            popCntxs <-  MV.unsafeRead (successorsCntxs globals) (gnId nextNode)
            mrPop <- IntSet.member (gnId nextNode) <$> readIORef (mustReachPop globals)
            return (popCntxs, mrPop)
        | (iVal > 0)  = merge globals nextNode >> return (IntSet.empty, True)
        | otherwise = error "unreachable error"
      follow e = do
        node <- liftIO $ MV.unsafeRead (supportGraph globals) (to e)
        iVal <- liftIO $ MV.unsafeRead (iVector globals) (to e)
        cases node iVal
  in do
    res <- forM (Set.toList $ internalEdges gn) follow
    let dPopCntxs = IntSet.unions (map fst res)
        dMustReachPop = all snd res
    let  computeActualRes
          | not . Set.null $ supportEdges gn = do
              newRes <- forM (Set.toList $ supportEdges gn) follow
              let actualDPopCntxs = IntSet.unions (map fst newRes)
              return (actualDPopCntxs, dMustReachPop && all snd newRes)
          | not . Map.null $ popContexts gn = return (IntSet.fromList . Map.keys $ popContexts gn, True)
          | otherwise = return (dPopCntxs, dMustReachPop)
    (dActualPopCntxs, dActualMustReachPop) <- computeActualRes
    createComponent globals gn (dActualPopCntxs, dActualMustReachPop) precFun query


-- helpers
addtoPath :: DeficientGlobals state -> GraphNode state -> Z3 ()
addtoPath globals gn = liftIO $ do
  ZS.push (sStack globals) (gnId gn)
  sSize <- ZS.size $ sStack globals
  MV.unsafeWrite (iVector globals) (gnId gn) sSize
  ZS.push (bStack globals) sSize

merge ::  DeficientGlobals state -> GraphNode state -> Z3 ()
merge globals gn = liftIO $ do
  iVal <- MV.unsafeRead (iVector globals) (gnId gn)
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  ZS.popWhile_ (bStack globals) (iVal <)

createComponent :: (Eq state, Hashable state, Show state)
                => DeficientGlobals state
                -> GraphNode state
                -> (SuccessorsPopContexts, Bool)
                -> EncPrecFunc
                -> TermQuery
                -> Z3 (SuccessorsPopContexts, Bool)
createComponent globals gn (popContxs, dMustReachPop) precFun query = do
  topB <- liftIO $ ZS.peek $ bStack globals
  iVal <- liftIO $ MV.unsafeRead (iVector globals) (gnId gn)
  let (varMap, encodeInitial) = partialVarMap globals
      createC = do
        liftIO $ ZS.pop_ (bStack globals)
        sSize <- liftIO $ ZS.size $ sStack globals
        poppedEdges <- liftIO $ ZS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        DBG.traceM  $ "Popped Semiconfigurations: " ++ show poppedEdges
        DBG.traceM $ "Pop contexts: " ++ show popContxs
        forM_ poppedEdges $ \e -> do
          liftIO $ MV.unsafeWrite (iVector globals) e (-1)
          liftIO $ MV.unsafeWrite (successorsCntxs globals) e popContxs
        return poppedEdges
      doEncode poppedEdges  = do
        currentASPSs <- liftIO $ readIORef (cannotReachPop globals)
        newAdded <- liftIO HT.new
        let to_be_encoded = [(gnId_, rc) | gnId_ <- poppedEdges, rc <- IntSet.toList popContxs]
        insertedUpperVars <- map snd <$> forM to_be_encoded (lookupVar (varMap, newAdded, currentASPSs, encodeInitial) (lowerEqMap globals, upperEqMap globals))
        insertedLowerVars <- map snd <$> forM to_be_encoded (lookupVar (varMap, newAdded, currentASPSs, encodeInitial) (lowerEqMap globals, upperEqMap globals))
        when (or insertedUpperVars || or insertedLowerVars) $ error "inserting a variable that has already been encoded"
        -- delete previous assertions and encoding the new ones
        reset >> encode to_be_encoded (varMap, newAdded, currentASPSs, encodeInitial) (lowerEqMap globals, upperEqMap globals) (supportGraph globals) precFun mkGe query
        actualMustReachPop <- solveSCCQuery poppedEdges dMustReachPop (varMap, newAdded, currentASPSs, encodeInitial) globals precFun
        when actualMustReachPop $ forM_ poppedEdges $ \e -> liftIO $ modifyIORef (mustReachPop globals) $ IntSet.insert e
        return (popContxs, actualMustReachPop)
      doNotEncode poppedEdges = do
        liftIO $ modifyIORef (cannotReachPop globals) $ IntSet.union (IntSet.fromList poppedEdges)
        when (gnId gn == 0 && encodeInitial) $ do -- for the initial semiconf, encode anyway
          newAdded <- liftIO HT.new
          currentASPSs <- liftIO $ readIORef (cannotReachPop globals)
          new_var <- mkFreshRealVar "(0,-1)" -- by convention, we give rightContext -1 to the initial state
          liftIO $ HT.insert varMap (0, -1) new_var
          reset >> encode [(0, -1)] (varMap, newAdded, currentASPSs, encodeInitial) (lowerEqMap globals, upperEqMap globals) (supportGraph globals) precFun mkGe query
          liftIO $ HT.insert newAdded (0 , -1) new_var
          False <- solveSCCQuery [0] False (varMap, newAdded, currentASPSs, encodeInitial) globals precFun
          return ()
        return (popContxs, False)
      cases
        | iVal /= topB = return (popContxs, dMustReachPop)
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases

-- params:
-- (var:: AST) = Z3 var associated with the initial semiconf
-- (graph :: SupportGraph RealWorld state :: ) = the graph
-- (varMap :: VarMap) = mapping (semiconf, rightContext) -> Z3 var
solveSCCQuery :: (Eq state, Hashable state, Show state)
              => [Int] -> Bool -> VarMap -> DeficientGlobals state -> EncPrecFunc -> Z3 Bool
solveSCCQuery sccMembers dMustReachPop varMap@(m, newAdded, _, _) globals precFun = do
  --DBG.traceM "Assert hints to solve the query"
  let epsVar = eps globals
      lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals
      rVarMap = rewVarMap globals

  currentEps <- liftIO $ readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  --eqMapList <- liftIO $ HT.toList eMap
  --DBG.traceM $ "Current equation system: \n" ++ concatMap (\l -> show l ++ "\n") eqMapList

  -- TODO: is it correct not to put inside z3 the lower bounds on variables? Who knows...
  _ <- preprocessApproxFixp lEqMap iterEps (2 * length sccMembers)
  updatedUpperVars <- preprocessApproxFixp uEqMap iterEps (2 * length sccMembers)
  forM_ updatedUpperVars $ \(varKey, p) -> do
    pAST <- mkRealNum (p :: Double)
    liftIO $ HT.insert m varKey pAST

  oviRes <- ovi defaultOVISettingsDouble uEqMap

  rCertified <- oviToRational defaultOVISettingsDouble uEqMap oviRes
  unless rCertified $ error "cannot deduce a rational certificate for this semiconf"

  unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the termination probabilities"

  {-
  DBG.traceM "Approximating via Value Iteration"
  approxVec <- approxFixp eqMap iterEps defaultMaxIters
  approxFracVec <- toRationalProbVec iterEps approxVec

  -- printing stuff - TO BE REMOVED
  forM_  approxFracVec $ \(varKey, _, p) -> do
      liftIO (HT.lookup eqMap varKey) >>= \case
        Just (PopEq _) -> return ()
        Just _ -> DBG.traceM ("Lower bound for " ++ show varKey ++ ": " ++ show p)
        _ -> error "weird error 1"

  nonPops <- filterM (\(varKey, _, _) -> do
        liftIO (HT.lookup eqMap varKey) >>= \case
          Just (PopEq _) -> return False
          Just _ -> return True
          _ -> error "weird error 2"
        ) approxFracVec

  -- TODO: if you restore this code, you will have to handle this by rehaving closing edges on the path
  let actualAsReachesPop = scclen < 2 && asReachesPop

  DBG.traceM "Asserting upper bounds 1 for value iteration"
  forM_ (groupBy (\k1 k2 -> fst k1 == fst k2) . map (\(varKey, _, _) -> varKey) $ nonPops) $ \list -> do
    sumVars <- mkAdd =<< liftIO (mapM (fmap fromJust . HT.lookup newAdded) list)
    assert =<< mkLe sumVars =<< mkRealNum (1 :: EqMapNumbersType)

  -- assert bounds computed by value iteration
  DBG.traceM "Asserting lower and upper bounds computed from value iteration, and getting a model"
  model <- doAssert approxFracVec eps

  -}

  variables <- liftIO $ map fst <$> HT.toList newAdded
  
  -- updating lower bounds
  approxVec <- approxFixp lEqMap iterEps defaultMaxIters
  forM_  variables $ \varKey -> do
    liftIO (HT.lookup lEqMap varKey) >>= \case
        Just (PopEq _) -> return () -- An eq constraint has already been asserted
        _ -> do
          p <- liftIO $ fromJust <$> HT.lookup approxVec varKey
          addFixpEq lEqMap varKey (PopEq p)

  -- updating upper bounds
  forM_ variables $ \varKey -> do
    ub <- liftIO $ min (1 :: Double) . fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
    ubAST <- mkRealNum ub
    liftIO $ HT.insert m varKey ubAST

  upperBound <- liftIO $ HT.toList (oviUpperBound oviRes)

  let upperBoundsTermProbs = (\mapAll -> Map.restrictKeys mapAll (IntSet.fromList sccMembers)) . Map.fromListWith (+) . map (\(key, ub) -> (fst key, ub)) $ upperBound
  let upperBounds = (\mapAll -> GeneralMap.restrictKeys mapAll (Set.fromList variables)) . GeneralMap.fromList $ upperBound
  DBG.traceM $ "Computed upper bounds: " ++ show upperBounds
  DBG.traceM $ "Computed upper bounds on termination probabilities: " ++ show upperBoundsTermProbs

  forM_  variables $ \varKey -> do
    liftIO (HT.lookup uEqMap varKey) >>= \case
        Just (PopEq _) -> return () -- An eq constraint has already been asserted
        _ -> do
          p <- liftIO $ fromJust <$> HT.lookup (oviUpperBound oviRes) varKey
          addFixpEq uEqMap varKey (PopEq p)

  -- computing the PAST certificate
  if not dMustReachPop || all (\(_,ub) -> ub < 1 - iterEps) (Map.toList upperBoundsTermProbs)
    then do
      unless (all (\(_,ub) -> ub < 1 - iterEps) (Map.toList upperBoundsTermProbs) || ((head variables) == (0 :: Int, -1 :: Int))) $ error "not AST but upper bound 1"
      return False
    else do
      let semiconfs = nub $ map fst variables
      insertedRewVars <- forM semiconfs $ \k -> do
          (_, b) <- lookupRewVar rVarMap k
          return (k,b)
      let to_be_encoded = map fst . filter (not . snd) $ insertedRewVars
      reset >> encodeReward to_be_encoded varMap rVarMap (supportGraph globals) precFun mkGe
      withModel (\model -> forM semiconfs $ \k -> do
          var <- liftIO $ fromJust <$> HT.lookup rVarMap k
          evaluated <- fromJust <$> eval model var
          liftIO $ HT.insert rVarMap k evaluated
        ) >>= \case
          (Unsat, _) -> DBG.traceM "PAST certification failed!" >> do
            unless (all (\(_,ub) -> ub < 1 - iterEps) (Map.toList upperBoundsTermProbs)) $ error "fail to prove PAST when some semiconfs have upper bounds on their termination equal to 1"
            return False
          (Sat, _) -> DBG.traceM "PAST certification succeeded!" >> do
            when (any (\(_,ub) -> ub < 1 - iterEps) (Map.toList upperBoundsTermProbs)) $ error "Found a PAST certificate for non AST semiconf!!"
            return True
          _ -> error "undefined result when running the past certificate"

  where
    doAssert approxFracVec currentEps = do
      push -- create a backtracking point
      epsReal <- mkRealNum currentEps

      forM_ approxFracVec (\(varKey, pRational, _) -> liftIO (HT.lookup (lowerEqMap globals) varKey) >>= \case
        Just (PopEq _) -> return () -- An eq constraint has already been asserted
        _ -> do
          (var, True) <- lookupVar varMap (lowerEqMap globals, upperEqMap globals) varKey
          pReal <- mkRealNum pRational
          assert =<< mkGe var pReal
          assert =<< mkLe var =<< mkAdd [pReal, epsReal])
      solverCheckAndGetModel >>= \case
        (Sat, Just model) -> return model
        (Unsat, _) -> liftIO (writeIORef (eps globals) (2 * currentEps)) >> pop 1 >> doAssert approxFracVec (2 * currentEps) -- backtrack one point and restart
        _ -> error "undefinite result when checking an SCC"


--- REWARDS COMPUTATION for certificating past ---------------------------------
type RewVarKey = Int
type RewVarMap = HT.BasicHashTable Int AST

-- (Z3 Var, was it already present?)
lookupRewVar :: RewVarMap -> RewVarKey -> Z3 (AST, Bool)
lookupRewVar rewVarMap key = do
  maybeVar <- liftIO $ HT.lookup rewVarMap key
  if isJust maybeVar
    then do
      return (fromJust maybeVar, True)
    else do
      new_var <- mkFreshRealVar $ show key
      liftIO $ HT.insert rewVarMap key new_var
      return (new_var, False)
-- end helpers


encodeReward :: (Eq state, Hashable state, Show state)
      => [RewVarKey]
      -> VarMap
      -> RewVarMap
      -> SupportGraph RealWorld state
      -> EncPrecFunc
      -> (AST -> AST -> Z3 AST)
      -> Z3 ()
encodeReward [] _ _ _ _ _ = return ()
encodeReward (gnId_:unencoded) varMap rewVarMap graph precFun mkComp = do
  rewVar <- liftIO $ fromJust <$> HT.lookup rewVarMap gnId_
  gn <- liftIO $ MV.unsafeRead graph gnId_
  let (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
          encodeRewPush graph varMap rewVarMap mkComp gn rewVar

        | precRel == Just Equal =
            encodeRewShift rewVarMap mkComp gn rewVar

        | precRel == Just Take = do
            assert =<< mkEq rewVar =<< mkRealNum (1 :: Prob)
            return [] -- pop transitions do not generate new variables

        | otherwise = fail "unexpected prec rel"

  new_unencoded <- cases
  encodeReward (new_unencoded ++ unencoded) varMap rewVarMap graph precFun mkComp

-- encoding helpers --
encodeRewPush :: (Eq state, Hashable state, Show state)
           => SupportGraph RealWorld state
           -> VarMap
           -> RewVarMap
           -> (AST -> AST -> Z3 AST)
           -> GraphNode state
           -> AST
           -> Z3 [RewVarKey]
encodeRewPush graph (m, _, asPendingIdxs ,_) rewVarMap mkComp gn var =
  let closeSummaries pushGn (currs, unencoded_vars) e = do
        supportGn <- liftIO $ MV.unsafeRead graph (to e)
        (summaryVar, alreadyEncoded) <- lookupRewVar rewVarMap (gnId supportGn)
        when (IntSet.member (gnId pushGn) asPendingIdxs ) $ error "trying to retrieve the termination prob of a semiconf that cannot reach a pop"
        termProb <- liftIO $ fromJust <$> HT.lookup m (gnId pushGn, getId . fst . semiconf $ supportGn)
        eq <- mkMul [termProb, summaryVar]
        return ( eq:currs
               ,  if alreadyEncoded then unencoded_vars else (gnId supportGn):unencoded_vars
               )
      pushEnc (currs, vars) e = do
        pushGn <- liftIO $ MV.unsafeRead graph (to e)
        (pushVar, alreadyEncoded) <- lookupRewVar rewVarMap (gnId pushGn)
        (equations, unencoded_vars) <- foldM (closeSummaries pushGn) ([], []) (supportEdges gn)
        transition <- encodeTransition e =<< mkAdd (pushVar:equations)
        return ( transition:currs
               , if alreadyEncoded then unencoded_vars ++ vars else (gnId pushGn) : (unencoded_vars ++ vars)
               )
  in do
    (transitions, unencoded_vars) <- foldM pushEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions) -- generate the equation for this semiconf
    assert =<< mkGe var one
    return unencoded_vars

encodeRewShift :: (Eq state, Hashable state, Show state)
  => RewVarMap
  -> (AST -> AST -> Z3 AST)
  -> GraphNode state
  -> AST
  -> Z3 [RewVarKey]
encodeRewShift rewVarMap mkComp gn var =
  let shiftEnc (currs, new_vars) e = do
        let target = to e
        (toVar, alreadyEncoded) <- lookupRewVar rewVarMap target
        trans <- encodeTransition e toVar
        return ( trans:currs
            , if alreadyEncoded then new_vars else target:new_vars
            )
  in do
    (transitions, unencoded_vars) <- foldM shiftEnc ([], []) (internalEdges gn)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions) -- generate the equation for this semiconf
    assert =<< mkGe var one
    return unencoded_vars
