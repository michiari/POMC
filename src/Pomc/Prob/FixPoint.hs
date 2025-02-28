{-# LANGUAGE HexFloatLiterals #-}
{- |
   Module      : Pomc.Prob.FixPoint
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.FixPoint ( VarKey
                          , FixpEq(..)
                          , EqMap
                          , AugEqMap
                          , LiveEq(..)
                          , LEqSys
                          , ProbVec
                          , addFixpEq
                          , addFixpEqs
                          , toLiveEqMapWith
                          , evalEqSys
                          , approxFixpFrom
                          , approxFixp
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          , preprocessApproxFixp
                          , containsEquation
                          , retrieveEquation
                          , retrieveEquationsIds
                          , liveVariables
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)
import Pomc.LogUtils (MonadLogger)

import Data.Maybe (fromJust, isJust)
import Data.Ratio (approxRational)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (modifyIORef', readIORef, IORef)

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as MM

import Data.Set (Set)
import qualified Data.Set as Set

-- a Map that is really strict
import qualified Data.Strict.Map as M
import Data.Foldable (foldl', foldMap')

import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Monoid (Sum(..))
import Data.IntSet (IntSet)
import qualified Data.IntMap as Map
import qualified Debug.Trace as DBG

type VarKey = (Int, Int)

data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

type EqMap n = IORef (IOMapMap (FixpEq n))
-- keep track of live equations for huge equation systems
type AugEqMap n = (EqMap n, IORef (Set VarKey))

-- EqMap containing only preprocessed live equations
-- (Left Int) is the variable's index in the current probVec, 
-- (Right n) is the supplied actual value for already solved variables
data LiveEq n = PushLEq [(n, Either Int n, Either Int n)]
              | ShiftLEq [(n, Either Int n)]
              deriving Show

type LEqSys n = Vector (LiveEq n)
type ProbVec n = Vector n

addFixpEq :: MonadIO m => AugEqMap n -> VarKey -> FixpEq n -> m ()
addFixpEq (eqMap, lEqs) varKey eq@(PopEq _) = liftIO $ do
  uncurry (MM.insert eqMap) varKey eq
  modifyIORef' lEqs (Set.delete varKey)
addFixpEq (eqMap, lEqs) varKey eq = liftIO $ do
  uncurry (MM.insert eqMap) varKey eq
  modifyIORef' lEqs (Set.insert varKey)

addFixpEqs :: (MonadIO m) => AugEqMap n -> Int -> Map.IntMap (FixpEq n) -> m ()
addFixpEqs  (eqMap, lEqs) semiconfId_ eqs = liftIO $ do
  MM.insertMap eqMap semiconfId_ eqs
  let isPopEq (PopEq _) = True 
      isPopEq _ = False
      liveVarKeys = [(semiconfId_, rc) | rc <- Map.keys . Map.filter (not . isPopEq) $ eqs]
      popVarKeys = [(semiconfId_, rc) | rc <- Map.keys . Map.filter (isPopEq) $ eqs]
  modifyIORef' lEqs (Set.union . Set.fromList $ liveVarKeys)
  modifyIORef' lEqs (\s -> Set.difference s (Set.fromList popVarKeys))

constructEitherWith :: (MonadIO m, Fractional k) => AugEqMap n -> VarKey -> Set VarKey -> (n -> k) -> m (Either Int k)
constructEitherWith (eqMap, _) k lVars f
  | (Just idx) <- Set.lookupIndex k lVars = return (Left idx)
  | otherwise = liftIO $ Right . (\(PopEq n) -> f n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

toLiveEqMapWith :: (MonadIO m, Fractional k) => AugEqMap n -> (n -> k) -> m (LEqSys k)
toLiveEqMapWith (eqMap, lEqs) f = liftIO $ do
  lVars <- readIORef lEqs
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        eitherK2 <- constructEitherWith (eqMap, lEqs) k2 lVars f
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        return (fromRational p, eitherK1)
      createEq k = do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> PushLEq <$> mapM createLivePush terms
          ShiftEq terms -> ShiftLEq <$> mapM createLiveShift terms
          _ -> error "A supposed live variable is actually dead"
  V.mapM createEq (V.fromList $ Set.toList lVars)

evalEqSys :: (Ord n, Fractional n)
          => LEqSys n -> (n -> n -> Bool) -> ProbVec n -> (Bool, ProbVec n)
evalEqSys leqMap checkRes src =
  let computEq (PushLEq terms) = getSum $ foldMap' 
            (\(p, k1, k2) -> Sum $ p * (either (src V.!) id k1) * (either (src V.!) id k2)
            ) terms
      computEq (ShiftLEq terms) = getSum $ foldMap'
            (\(p, k1) -> Sum $ p * either (src V.!) id k1) terms

      dest = V.map computEq leqMap
      checkDest = V.and (V.zipWith checkRes dest src)
  in (checkDest, dest)

approxFixpFrom :: (Ord n, Fractional n, Show n)
               => LEqSys n -> n -> Int -> ProbVec n -> ProbVec n
approxFixpFrom leqMap eps maxIters probVec
  | maxIters <= 0 = probVec
  | otherwise =
      -- should be newV >= oldV
      let checkIter newV oldV =
            -- newV - oldV <= eps -- absolute error
            newV == 0 || (newV - oldV) / newV <= eps -- relative error
          (lessThanEps, newProbVec) = evalEqSys leqMap checkIter probVec
      in if lessThanEps
          then newProbVec
          else approxFixpFrom leqMap eps (maxIters - 1) newProbVec

-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n, Show k)
                      => AugEqMap k -> (k -> n) -> n -> Int -> m ([(VarKey, n)], [VarKey])
preprocessApproxFixp augEqMap@(_, lVarsRef) f eps maxIters = do
  lVars <- liftIO $ readIORef lVarsRef
  if Set.null lVars
    then return ([],[])
    else do
      leqMap <- toLiveEqMapWith augEqMap f
      let probVec = approxFixpFrom leqMap eps maxIters (V.replicate (Set.size lVars) 0)
          (zeroVec, nonZeroVec) = V.unstablePartition (\(_,_,p) -> p == 0) $ V.zip3 (V.fromList $ Set.toList lVars) leqMap probVec
          isLiveSys = not (V.null nonZeroVec)

          solveShift _ Nothing _ = Nothing
          solveShift _ (Just acc) (p, Right v) = Just $ acc + p * v
          solveShift killedVars (Just acc) (p, Left idx)
            | (Just v) <- M.lookup k killedVars = Just $ acc + p * v
            | otherwise = Nothing
              where k = Set.elemAt idx lVars

          solvePush _ Nothing _ = Nothing
          solvePush _ (Just acc) (p, Right v1, Right v2) = Just $ acc + p * v1 * v2
          solvePush killedVars (Just acc) (p, Right v1, Left idx)
            | (Just v) <- M.lookup k killedVars = Just $ acc + p * v1 * v
            | otherwise = Nothing
              where k = Set.elemAt idx lVars
          solvePush killedVars (Just acc) (p, Left k, Right v1) = solvePush killedVars (Just acc) (p, Right v1, Left k)
          solvePush killedVars (Just acc) (p, Left idx1, Left idx2)
            | (Just v1) <- M.lookup k1 killedVars, (Just v2) <- M.lookup k2 killedVars = Just $ acc + p * v1 * v2
            | otherwise = Nothing
              where k1 = Set.elemAt idx1 lVars
                    k2 = Set.elemAt idx2 lVars

          solveEq killedVars eq = case eq of
            PushLEq terms ->  foldl' (solvePush killedVars)  (Just 0) terms
            ShiftLEq terms -> foldl' (solveShift killedVars) (Just 0) terms

          go (False, updatedVars, liveVars)  = (M.toList updatedVars, map fst liveVars)
          go (True, updatedVars, liveVars) = go $ foldl' (\(recurse, upVars, lVars) (varKey, eq) ->
            case solveEq updatedVars eq of
              Nothing -> (recurse, upVars, (varKey, eq):lVars)
              Just v  -> (True, M.insert varKey v upVars, lVars)

            ) (False, updatedVars, []) liveVars

          -- preprocess live equations by propagating found values, until no value
          zeroVars = M.fromList . V.toList . V.map (\(k,_,p) -> (k,p)) $ zeroVec
          nonZeroVars = V.toList . V.map (\(k,eq, _) -> (k,eq)) $ nonZeroVec
          (upVars, newLiveVars) = go (isLiveSys, zeroVars, nonZeroVars)
      return (upVars, newLiveVars)

approxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n)
           => AugEqMap k -> (k -> n) -> n -> Int -> m (ProbVec n)
approxFixp augEqMap f eps maxIters = do
  leqMap <- toLiveEqMapWith augEqMap f
  return $ approxFixpFrom leqMap eps maxIters (V.replicate (V.length leqMap) 0)
   
defaultEps :: EqMapNumbersType
defaultEps = 0x1p-26 -- ~ 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (RealFrac n) => n -> ProbVec n -> ProbVec Prob
toRationalProbVec eps = V.map (\p -> approxRational (p - eps) eps)
-- p - eps is to prevent approxRational from producing a result > p

containsEquation :: (MonadIO m) => AugEqMap n -> VarKey -> m Bool
containsEquation (eqMap, _) varKey = liftIO $ uncurry (MM.member eqMap) varKey

retrieveEquation :: (MonadIO m) => AugEqMap n -> VarKey -> m (Maybe (FixpEq n))
retrieveEquation (eqMap, _) varKey = liftIO $ uncurry (MM.lookupValue eqMap) varKey

retrieveEquationsIds :: (MonadIO m) => AugEqMap n -> Int -> m IntSet
retrieveEquationsIds (eqMap, _) semiconfId_ = liftIO $ MM.lookupKeys eqMap semiconfId_

liveVariables :: (MonadIO m) => AugEqMap n ->  m (Vector VarKey)
liveVariables (_,lVarsRef) = V.fromList . Set.toList <$> liftIO (readIORef lVarsRef)