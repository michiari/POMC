{-# LANGUAGE LambdaCase #-}
{- |
   Module      : Pomc.Prob.Runtime
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Runtime( certifyPAST
                        , RewVarMap
                        ) where

import Prelude hiding (LT, GT)
import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint (retrieveEquations, FixpEq (PopEq), EqMap)
import Pomc.LogUtils (logDebugN, MonadLogger)

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.Vector((!))
import qualified Data.HashTable.IO as HT

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (foldM, forM, when, forM_, unless)
import Data.Maybe(fromJust, isJust, mapMaybe)
import Z3.Monad

--- Computing the expected runtime to certify PAST ---------------------------------
-- Reference: "On Certificates, Expected Runtimes, and Termination Probabilities of pPDA", 
-- LICS 2023, Winkler and Katoen, Theorem 7
type RewVarKey = Int -- semiconfId_
type RewVarMap = HT.BasicHashTable Int AST

certifyPAST :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => [Int]
  -> EqMap (Double, Double)
  -> RewVarMap
  -> SupportGraph state
  -> (AST -> AST -> z3 AST)
  -> Bool
  -> z3 Bool
certifyPAST sccMembers eqMap rVarMap suppGraph mkComp expectPAST = do 
  -- preadding all equations
  forM_ sccMembers $ \k -> do
    (_, alreadyEnc) <- lookupRewVar rVarMap k
    when alreadyEnc $ 
      error "Encoding reward variable for a semiconf that has already been encoded."
  -- encoding all equations
  reset
  encodeReward sccMembers eqMap rVarMap suppGraph mkComp
  withModel (\model -> forM sccMembers $ \id_ -> do
                          var <- liftIO $ fromJust <$> HT.lookup rVarMap id_
                          evaluated <- fromJust <$> eval model var
                          liftIO $ HT.insert rVarMap id_ evaluated
                              ) >>= \case
    (Unsat, _) -> error "Fail to prove PAST."
    (Sat, _) -> do
      unless expectPAST $ error "Found a PAST certificate for a SCC which has upper bounds on termination probabilities proving non-AST."
      logDebugN "PAST certification succeeded."
      return True
    _ -> error "Undefined result when running the PAST certificate."
  
--helpers
-- (Z3 Var, was it already present?)
lookupRewVar :: MonadZ3 z3 => RewVarMap -> RewVarKey -> z3 (AST, Bool)
lookupRewVar rVarMap key = do
  maybeVar <- liftIO $ HT.lookup rVarMap key
  if isJust maybeVar
    then return (fromJust maybeVar, True)
    else do
      newVar <- mkFreshRealVar $ show key
      liftIO $ HT.insert rVarMap key newVar
      return (newVar, False)

encodeTransition :: MonadZ3 z3 => Prob -> AST -> z3 AST
encodeTransition prob_ toAST = do
  probReal <- mkRealNum prob_
  mkMul [probReal, toAST]
-- end helpers

encodeReward :: (MonadZ3 z3, MonadFail z3)
  => [RewVarKey]
  -> EqMap (Double, Double)
  -> RewVarMap
  -> SupportGraph state
  -> (AST -> AST -> z3 AST)
  -> z3 ()
encodeReward [] _ _ _ _ = return ()
encodeReward (gnId_:unencoded) eqMap rVarMap suppGraph mkComp = do
  rewVar <- liftIO $ fromJust <$> HT.lookup rVarMap gnId_
  let gn = suppGraph ! gnId_
      transitionCases (Push suppSet pushMap) = 
        encodeRewPush suppGraph eqMap rVarMap mkComp suppSet pushMap rewVar
      transitionCases (Shift shiftMap) = 
        encodeRewShift rVarMap mkComp shiftMap rewVar
      transitionCases (Pop _) = do -- reward is trivially 1
        assert =<< mkEq rewVar =<< mkRealNum (1 :: Prob)
        return []

  newUnencoded <- transitionCases (gnEdges gn)
  encodeReward (newUnencoded ++ unencoded) eqMap rVarMap suppGraph mkComp

-- encoding helpers --
encodeRewPush :: (MonadZ3 z3)
  => SupportGraph state
  -> EqMap (Double, Double)
  -> RewVarMap
  -> (AST -> AST -> z3 AST)
  -> IntSet
  -> IntMap Prob
  -> AST
  -> z3 [RewVarKey]
encodeRewPush suppGraph eqMap rVarMap mkComp suppSet pushMap var = do
  pushInfo <- forM (IntMap.toList pushMap) (\(id_, prob_) -> do
    (pushVar, alrEnc) <- lookupRewVar rVarMap id_
    -- if we can find a solution with upper bound coefficient, 
    -- this solution holds also for the actual (uncomputable) coefficients
    rcs <- liftIO $ retrieveEquations eqMap id_ 
    encodedRcs <- forM rcs $ \(pushRC, PopEq (_,ub)) -> do 
      ubAST <- mkRealNum (ub :: Double)
      return (pushRC, ubAST)
      
    return (prob_, pushVar, encodedRcs, if alrEnc then Nothing else Just id_))

  suppInfo <- forM (IntSet.toList suppSet) (\id_ -> do
    (suppVar, alrEnc) <- lookupRewVar rVarMap id_
    let suppStateId_ = getId . fst . semiconf $ suppGraph ! id_
    return (suppStateId_, suppVar, if alrEnc then Nothing else Just id_))

  let unencPushVars = mapMaybe (\(_,_, _, maybeId_) -> maybeId_) pushInfo
      unencSuppVars = mapMaybe (\(_, _, maybeId_) -> maybeId_) suppInfo

  let terms = [(prob_,pushVar,
                    [[termVar,suppVar] |
                       (pushRC, termVar) <- rcs
                     , (suppStateId_, suppVar, _) <- suppInfo
                     , pushRC == suppStateId_
                    ]) |
                  (prob_, pushVar, rcs, _) <- pushInfo
             ]
  transitions <- forM terms (\(prob_,pushVar, suppTerms) -> do
    encodeTransition prob_ =<< (mkAdd . (pushVar :) =<< mapM mkMul suppTerms))
  one <- mkRealNum (1 :: Prob)
  assert =<< mkComp var =<< mkAdd (one:transitions)
  assert =<< mkGe var one
  return (unencSuppVars ++ unencPushVars)

encodeRewShift :: MonadZ3 z3
  => RewVarMap
  -> (AST -> AST -> z3 AST)
  -> IntMap Prob
  -> AST
  -> z3 [RewVarKey]
encodeRewShift rVarMap mkComp shiftMap var =
  let shiftEnc (currTs, newVars) (id_, prob_) = do
        (toVar, alrEnc) <- lookupRewVar rVarMap id_
        t <- encodeTransition prob_ toVar
        return (t:currTs, if alrEnc then newVars else id_:newVars)
  in do
    (transitions, unencVars) <- foldM shiftEnc ([], []) (IntMap.toList shiftMap)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions)
    assert =<< mkGe var one
    return unencVars
