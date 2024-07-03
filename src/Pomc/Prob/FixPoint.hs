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
                          , newVecSameSize
                          , mapVec
                          , copyVec
                          , zeroLiveVec
                          , lookupValue
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

import Data.Maybe (fromJust, isJust)
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

import Data.Bifunctor(first)

type VarKey = (Int, Int)

data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

type EqMap n = IORef (IOMapMap Int (FixpEq n))
-- keep track of live equations for huge equation systems
type AugEqMap n = (EqMap n, IORef (Set VarKey))

-- EqMap containing only preprocessed live equations
data LiveEq n = PushLEq [(n, VarKey, VarKey)]
              | ShiftLEq [(n, VarKey)]
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

toLiveEqMap :: (MonadIO m, Fractional n, Fractional k) => AugEqMap n -> m (LEqSys k)
toLiveEqMap (eqMap, lEqs) = liftIO $ do
  lVars <- readIORef lEqs
  leqMap <- MV.unsafeNew (Set.size lVars)
  foldM_
    (\i k -> do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> MV.unsafeWrite leqMap i
                          (k, PushLEq $ map (\(p, k1, k2) -> (fromRational p, k1, k2)) terms)
                          >> return (i + 1)
          ShiftEq terms -> MV.unsafeWrite leqMap i
                           (k, ShiftLEq $ map (first fromRational) terms)
                           >> return (i + 1)
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

zeroLiveVec :: (MonadIO m, Fractional n) => AugEqMap n -> m (ProbVec n)
zeroLiveVec (eqMap, lEqs) = liftIO $ do
  lVars <- readIORef lEqs
  probVec <- HT.newSized (Set.size lVars)
  forM_ (Set.toList lVars) $ \k -> do
    eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
    case eq of
               PopEq _ -> error "an equation is marked as live but it is actually not"
               _ -> HT.insert probVec k 0
  return probVec

lookupValue :: MonadIO m => AugEqMap k -> (k -> n) -> ProbVec n -> VarKey ->  m n
lookupValue (eqMap, lEqs) f probV k = liftIO $ do
  lVars <- readIORef lEqs
  if Set.member k lVars
    then fromJust <$> HT.lookup probV k
    else f . (\(PopEq n) -> n) . fromJust <$> uncurry (MM.lookupValue eqMap) k


evalEqSys :: (MonadIO m, Ord n, Fractional n, Ord k, Fractional k)
          => AugEqMap k -> (k -> n) -> LEqSys n -> (Bool -> n -> n -> Bool) -> ProbVec n -> ProbVec n -> m Bool
evalEqSys (eqMap, lEqs) f leqMap checkRes src dst = liftIO $ MV.foldM' evalEq True leqMap where
  evalEq prevCheck (key, eq) = do
    oldV <- fromJust <$> HT.lookup src key
    newV <- case eq of
      PushLEq terms -> sum <$> mapM
        (\(p, k1, k2) -> do
            v1 <- lookupValue (eqMap, lEqs) f src k1
            v2 <- lookupValue (eqMap, lEqs) f src k2
            return $ p * v1 * v2
        ) terms
      ShiftLEq terms -> sum <$> mapM (\(p, k) -> (p *) <$> lookupValue (eqMap, lEqs) f src k) terms
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
      lessThanEps <- evalEqSys augEqMap id leqMap checkIter probVec probVec
      unless lessThanEps $ approxFixpFrom augEqMap leqMap eps (maxIters - 1) probVec

-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
                      => AugEqMap n -> n -> Int -> m ([(VarKey, n)], [VarKey])
preprocessApproxFixp augEqMap@(eqMap, lVarsRef) eps maxIters = do
  probVec <- zeroLiveVec augEqMap
  leqMap <- toLiveEqMap augEqMap
  -- iterate just n and check if fixpoint remains zero
  approxFixpFrom augEqMap leqMap eps maxIters probVec
  (zeroVars, nonZeroVars) <- liftIO $ MV.foldM (\(acc1, acc2) (varKey, _) -> do
                                p <- fromJust <$> HT.lookup probVec varKey
                                if p == 0
                                  then do
                                    uncurry (MM.insert eqMap) varKey (PopEq 0)
                                    modifyIORef' lVarsRef (Set.delete varKey)
                                    return (varKey:acc1, acc2)
                                  else return (acc1, varKey:acc2)
                                ) ([], []) leqMap

  let isLiveSys = not (null nonZeroVars)

      computeShift Nothing _ = return Nothing
      computeShift (Just acc) (p, k1) = do
          isLive <- Set.member k1 <$> readIORef lVarsRef
          if isLive
            then return Nothing
            else (\(PopEq n) -> Just $ acc + (fromRational p) * n) . fromJust <$> uncurry (MM.lookupValue eqMap) k1

      computePush Nothing _ = return Nothing
      computePush (Just acc) (p, k1, k2) = do
          isLivek1 <- Set.member k1 <$> readIORef lVarsRef
          isLivek2 <- Set.member k2 <$> readIORef lVarsRef
          if isLivek1 || isLivek2
            then return Nothing
            else do
              k1Value <- (\(PopEq n) -> n) . fromJust <$> uncurry (MM.lookupValue eqMap) k1
              k2Value <- (\(PopEq n) -> n) . fromJust <$> uncurry (MM.lookupValue eqMap) k2
              return $ Just $ acc + (fromRational p) * k1Value * k2Value

      killVar varKey Nothing (recurse, upVars, lVars) = return (recurse, upVars, varKey: lVars)
      killVar varKey (Just eqValue) (_, upVars, lVars) = do
        uncurry (MM.insert eqMap) varKey (PopEq eqValue)
        modifyIORef' lVarsRef (Set.delete varKey)
        return (True, (varKey, eqValue) : upVars, lVars)

      go (False, updatedVars, liveVars)  = return (updatedVars ++ map (\v -> (v,0)) zeroVars, liveVars)
      go (True, updatedVars,liveVars) = foldM (\(recurse, upVars, lVars) varKey -> do
          eq <- fromJust <$> uncurry (MM.lookupValue eqMap) varKey
          case eq of
            PopEq _ -> error "this is not a live variable"
            ShiftEq terms -> do
              value <- foldM computeShift (Just 0) terms
              killVar varKey value (recurse, upVars, lVars)
            PushEq terms -> do
              value <- foldM computePush (Just 0) terms
              killVar varKey value (recurse, upVars, lVars)
        ) (False, updatedVars, []) liveVars >>= go
  liftIO $ go (isLiveSys, [], nonZeroVars)

approxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
           => AugEqMap n -> n -> Int -> m (ProbVec n)
approxFixp augEqMap eps maxIters = do
  probVec <- zeroLiveVec augEqMap
  leqMap <- toLiveEqMap augEqMap
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
