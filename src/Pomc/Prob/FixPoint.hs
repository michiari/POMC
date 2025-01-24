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
                          , newVecSameSize
                          , mapVec
                          , copyVec
                          , zeroLiveVec
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

import Data.Maybe (fromJust)
import Data.Ratio (approxRational)
import Control.Monad ( unless, foldM, forM_, foldM_)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as MM

import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IORef (modifyIORef', readIORef, IORef)

-- a Map that is really strict
import qualified Data.Strict.Map as M
import Data.Foldable (foldl')


type VarKey = (Int, Int)

data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

type EqMap n = IORef (IOMapMap Int (FixpEq n))
-- keep track of live equations for huge equation systems
type AugEqMap n = (EqMap n, IORef (Set VarKey))

-- EqMap containing only preprocessed live equations
data LiveEq n = PushLEq [(n, Either VarKey n, Either VarKey n)]
              | ShiftLEq [(n, Either VarKey n)]
              deriving Show
type LEqSys n = IOVector (VarKey, LiveEq n)

type ProbVec n = HT.BasicHashTable VarKey n

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

constructEither :: (MonadIO m, Fractional n) => AugEqMap n -> VarKey -> Set VarKey -> m (Either VarKey n)
constructEither (eqMap, _) k lVars
  | Set.member k lVars = return (Left k)
  | otherwise = liftIO $ Right . (\(PopEq n) -> n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

constructEitherWith :: (MonadIO m, Fractional n, Fractional k) => AugEqMap n -> VarKey -> Set VarKey -> (n -> k) -> m (Either VarKey k)
constructEitherWith (eqMap, _) k lVars f
  | Set.member k lVars = return (Left k)
  | otherwise = liftIO $ Right . (\(PopEq n) -> f n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

toLiveEqMap :: (MonadIO m, Fractional n) => AugEqMap n -> m (LEqSys n)
toLiveEqMap (eqMap, lEqs) = liftIO $ do
  lVars <- readIORef lEqs
  leqMap <- MV.unsafeNew (Set.size lVars)
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEither (eqMap, lEqs) k1 lVars
        eitherK2 <- constructEither (eqMap, lEqs) k2 lVars
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEither (eqMap, lEqs) k1 lVars
        return (fromRational p, eitherK1)
  foldM_
    (\i k -> do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> do
            liveTerms <- mapM createLivePush terms
            MV.unsafeWrite leqMap i (k, PushLEq liveTerms)
            return (i + 1)
          ShiftEq terms -> do
            liveTerms <- mapM createLiveShift terms
            MV.unsafeWrite leqMap i (k, ShiftLEq liveTerms)
            return (i + 1)
          _ -> error "A supposed live variable is actually dead"
    ) 0 lVars
  return leqMap

toLiveEqMapWith :: (MonadIO m, Fractional n, Fractional k) => AugEqMap n -> (n -> k) -> m (LEqSys k)
toLiveEqMapWith (eqMap, lEqs) f = liftIO $ do
  lVars <- readIORef lEqs
  leqMap <- MV.unsafeNew (Set.size lVars)
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        eitherK2 <- constructEitherWith (eqMap, lEqs) k2 lVars f
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        return (fromRational p, eitherK1)
  foldM_
    (\i k -> do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> do
            liveTerms <- mapM createLivePush terms
            MV.unsafeWrite leqMap i (k, PushLEq liveTerms)
            return (i + 1)
          ShiftEq terms -> do
            liveTerms <- mapM createLiveShift terms
            MV.unsafeWrite leqMap i (k, ShiftLEq liveTerms)
            return (i + 1)
          _ -> error "A supposed live variable is actually dead"
    ) 0 lVars
  return leqMap

newVecSameSize :: MonadIO m => ProbVec a -> m (ProbVec b)
newVecSameSize vec = liftIO $ HT.newSized =<< stToIO (BHT.size vec)

mapVec :: MonadIO m => (a -> b) -> ProbVec a -> m (ProbVec b)
mapVec f vec = liftIO $ do
  newVec <- HT.newSized =<< stToIO (BHT.size vec)
  HT.mapM_ (\(k, v) -> HT.insert newVec k $ f v) vec
  return newVec

copyVec :: MonadIO m => ProbVec n -> m (ProbVec n)
copyVec = mapVec id

-- a vector of 0 for all live equations
zeroLiveVec :: (MonadIO m, Fractional n) => AugEqMap n -> m (ProbVec n)
zeroLiveVec (_, lEqs) = liftIO $ do
  lVars <- readIORef lEqs
  probVec <- HT.newSized (Set.size lVars)
  forM_ (Set.toList lVars) $ \k -> HT.insert probVec k 0
  -- adding also values they depend on, it will be useful for latel
  return probVec

evalEqSys :: (MonadIO m, Ord n, Fractional n)
          => LEqSys n -> (Bool -> n -> n -> Bool) -> ProbVec n -> ProbVec n -> m Bool
evalEqSys leqMap checkRes src dst = liftIO $ MV.foldM' evalEq True leqMap where
  evalEq prevCheck (key, eq) = do
    oldV <- fromJust <$> HT.lookup src key
    newV <- case eq of
      PushLEq terms -> sum <$> mapM
        (\(p, k1, k2) -> do
            v1 <- either (fmap fromJust . HT.lookup src) return k1
            v2 <- either (fmap fromJust . HT.lookup src) return k2
            return $ p * v1 * v2
        ) terms
      ShiftLEq terms -> sum <$> mapM (\(p, k1) -> (p *) <$> either (fmap fromJust . HT.lookup src) return k1) terms
    HT.insert dst key newV
    return $ checkRes prevCheck newV oldV

approxFixpFrom :: (MonadIO m, Ord n, Fractional n, Show n)
               => AugEqMap n -> LEqSys n -> n -> Int -> ProbVec n -> m ()
approxFixpFrom augEqMap leqMap eps maxIters probVec
  | maxIters <= 0 = return ()
  | otherwise = do
      -- should be newV >= oldV
      let checkIter leqEps newV oldV =
            -- leqEps && newV - oldV <= eps -- absolute error
            leqEps && (newV == 0 || (newV - oldV) / newV <= eps) -- relative error
      lessThanEps <- evalEqSys leqMap checkIter probVec probVec
      unless lessThanEps $ approxFixpFrom augEqMap leqMap eps (maxIters - 1) probVec

-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
                      => AugEqMap n -> n -> Int -> m ([(VarKey, n)], [VarKey])
preprocessApproxFixp augEqMap@(eqMap, lVarsRef) eps maxIters = do
  lVars <- liftIO $ readIORef lVarsRef
  if Set.null lVars
    then return ([],[])
    else do
      leqMap <- toLiveEqMap augEqMap
      probVec <- zeroLiveVec augEqMap

      -- iterate just n and check if fixpoint remains zero
      approxFixpFrom augEqMap leqMap eps maxIters probVec

      (zeroVars, nonZeroVars) <- liftIO $ MV.foldM (\(acc1, acc2) (varKey, eq) -> do
                                    p <- fromJust <$> HT.lookup probVec varKey
                                    if p == 0
                                      then do
                                        uncurry (MM.insert eqMap) varKey (PopEq 0)
                                        modifyIORef' lVarsRef (Set.delete varKey)
                                        return (M.insert varKey 0 acc1, acc2)
                                      else return (acc1, (varKey, eq):acc2)
                                    ) (M.empty, []) leqMap

      let isLiveSys = not (null nonZeroVars) 

          solveShift _ Nothing _ = Nothing
          solveShift _ (Just acc) (p, (Right v)) = Just $ acc + p * v
          solveShift killedVars (Just acc) (p, ( Left k))
            | M.member k killedVars = Just $ acc + p * ((M.!) killedVars k)
            | otherwise = Nothing

          solvePush _ Nothing _ = Nothing
          solvePush _ (Just acc) (p, (Right v1), (Right v2)) = Just $ acc + p * v1 * v2
          solvePush killedVars (Just acc) (p, (Right v1), (Left k))
            | M.member k killedVars = Just $ acc + p * v1 * ((M.!) killedVars k)
            | otherwise = Nothing
          solvePush killedVars (Just acc) (p, (Left k), (Right v1)) = solvePush killedVars (Just acc) (p, (Right v1), (Left k))
          solvePush killedVars (Just acc) (p, (Left k1), (Left k2))
            | M.member k1 killedVars && M.member k2 killedVars = Just $ acc + p * ((M.!) killedVars k2) * ((M.!) killedVars k1)
            | otherwise = Nothing

          solveEq killedVars eq = case eq of 
            PushLEq terms ->  foldl' (solvePush killedVars)  (Just 0) terms
            ShiftLEq terms -> foldl' (solveShift killedVars) (Just 0) terms

          go (False, updatedVars, liveVars)  = (M.toList updatedVars, map fst liveVars)
          go (True, updatedVars, liveVars) = go $ foldl' (\(recurse, upVars, lVars) (varKey, eq) -> 
            case (solveEq updatedVars eq) of 
              Nothing -> (recurse, upVars, (varKey, eq):lVars)
              Just v  -> (True, M.insert varKey v upVars, lVars)

            ) (False, updatedVars, []) liveVars
            
          -- preprocess live equations by propagating found values, until no value
          (upVars, lVars) = go (isLiveSys, zeroVars, nonZeroVars)
      liftIO $ forM_ upVars $ \(k, p) -> do
        uncurry (MM.insert eqMap) k (PopEq p)
        modifyIORef' lVarsRef (Set.delete k)
      return (upVars, lVars)


approxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
           => AugEqMap n -> n -> Int -> m (ProbVec n)
approxFixp augEqMap eps maxIters = do
  leqMap <- toLiveEqMap augEqMap
  probVec <- zeroLiveVec augEqMap
  approxFixpFrom augEqMap leqMap eps maxIters probVec
  return probVec

defaultEps :: EqMapNumbersType
defaultEps = 0x1p-26 -- ~ 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (MonadIO m, RealFrac n) => n -> ProbVec n -> m [(VarKey, Prob)]
toRationalProbVec eps probVec = liftIO $ HT.foldM (\acc (lVar, p) -> return ((lVar, approxRational (p - eps) eps) : acc) ) [] probVec
-- p - eps is to prevent approxRational from producing a result > p

containsEquation :: (MonadIO m, RealFrac n) => AugEqMap n -> VarKey -> m Bool
containsEquation (eqMap, _) varKey = liftIO $ uncurry (MM.member eqMap) varKey
