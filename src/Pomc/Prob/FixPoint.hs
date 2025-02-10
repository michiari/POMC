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
                          , deleteFixpEq
                          , toLiveEqMap
                          , toLiveEqMapWith
                          , evalEqSys
                          , approxFixpFrom
                          , approxFixp
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          , preprocessApproxFixp
                          , containsEquation
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)
import Pomc.LogUtils (MonadLogger)

import Data.Maybe (fromJust)
import Data.Ratio (approxRational)
import Control.Monad (forM_)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (modifyIORef', readIORef, IORef)

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as MM

import Data.Set (Set)
import qualified Data.Set as Set

-- a Map that is really strict
import qualified Data.Strict.Map as M
import Data.Foldable (foldl')

import Data.Vector (Vector)
import qualified Data.Vector as V

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

deleteFixpEq :: MonadIO m => AugEqMap n -> VarKey -> m ()
deleteFixpEq (eqMap, lEqs) varKey = liftIO $ do
  MM.delete eqMap varKey
  modifyIORef' lEqs (Set.delete varKey)

constructEither :: (MonadIO m, MonadLogger m, Fractional n) => AugEqMap n -> VarKey -> Set VarKey -> m (Either Int n)
constructEither (eqMap, _) k lVars
  | (Just idx) <- Set.lookupIndex k lVars = return (Left idx)
  | otherwise = liftIO $ Right . (\(PopEq n) -> n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

constructEitherWith :: (MonadIO m, Fractional n, Fractional k) => AugEqMap n -> VarKey -> Set VarKey -> (n -> k) -> m (Either Int k)
constructEitherWith (eqMap, _) k lVars f
  | (Just idx) <- Set.lookupIndex k lVars = return (Left idx)
  | otherwise = liftIO $ Right . (\(PopEq n) -> f n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

toLiveEqMap :: (MonadIO m, MonadLogger m, Fractional n) => AugEqMap n -> m (LEqSys n)
toLiveEqMap (eqMap, lEqs) = do
  lVars <- liftIO $ readIORef lEqs
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEither (eqMap, lEqs) k1 lVars
        eitherK2 <- constructEither (eqMap, lEqs) k2 lVars
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEither (eqMap, lEqs) k1 lVars
        return (fromRational p, eitherK1)
      createEq k = do
        eq <- liftIO $ fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> PushLEq <$> mapM createLivePush terms
          ShiftEq terms -> ShiftLEq <$> mapM createLiveShift terms
          _ -> error "A supposed live variable is actually dead"
  V.mapM createEq (V.fromList $ Set.toList lVars)

toLiveEqMapWith :: (MonadIO m, Fractional n, Fractional k) => AugEqMap n -> (n -> k) -> m (LEqSys k)
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
  let computEq eq 
        | (PushLEq terms) <- eq = sum $ map
            (\(p, k1, k2) -> p * (either (src V.!) id k1) * (either (src V.!) id k2)
            ) terms
        | (ShiftLEq terms) <- eq = sum $ map
            (\(p, k1) -> p * either (src V.!) id k1) terms

      dest = V.map computEq leqMap
      checkDest = V.all (uncurry checkRes) (V.zip dest src)
  in (checkDest, dest)

approxFixpFrom :: (Ord n, Fractional n, Show n)
               => AugEqMap n -> LEqSys n -> n -> Int -> ProbVec n -> ProbVec n
approxFixpFrom augEqMap leqMap eps maxIters probVec
  | maxIters <= 0 = probVec
  | otherwise =
      -- should be newV >= oldV
      let checkIter newV oldV =
            -- newV - oldV <= eps -- absolute error
            newV == 0 || (newV - oldV) / newV <= eps -- relative error
          (lessThanEps, newProbVec) = evalEqSys leqMap checkIter probVec
      in if lessThanEps
          then newProbVec
          else approxFixpFrom augEqMap leqMap eps (maxIters - 1) newProbVec

-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n)
                      => AugEqMap n -> n -> Int -> m ([(VarKey, n)], [VarKey])
preprocessApproxFixp augEqMap@(eqMap, lVarsRef) eps maxIters = do
  lVars <- liftIO $ readIORef lVarsRef
  if Set.null lVars
    then return ([],[])
    else do
      leqMap <- toLiveEqMap augEqMap
      let probVec = approxFixpFrom augEqMap leqMap eps maxIters (V.replicate (Set.size lVars) 0)
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

      liftIO $ forM_ upVars $ \(k, p) -> do
        uncurry (MM.insert eqMap) k (PopEq p)
        modifyIORef' lVarsRef (Set.delete k)

      return (upVars, newLiveVars)

approxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n)
           => AugEqMap n -> n -> Int -> m (ProbVec (VarKey, n))
approxFixp augEqMap@(_,lVarsRef) eps maxIters = do
  leqMap <- toLiveEqMap augEqMap
  let probVec = approxFixpFrom augEqMap leqMap eps maxIters (V.replicate (V.length leqMap) 0)
  lVars <- liftIO $ readIORef lVarsRef
  return (V.zip (V.fromList . Set.toList $ lVars) probVec)

defaultEps :: EqMapNumbersType
defaultEps = 0x1p-26 -- ~ 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (RealFrac n) => n -> ProbVec (VarKey, n) -> ProbVec (VarKey, Prob)
toRationalProbVec eps = V.map (\(k, p) -> (k, approxRational (p - eps) eps))
-- p - eps is to prevent approxRational from producing a result > p

containsEquation :: (MonadIO m, RealFrac n) => AugEqMap n -> VarKey -> m Bool
containsEquation (eqMap, _) varKey = liftIO $ uncurry (MM.member eqMap) varKey
