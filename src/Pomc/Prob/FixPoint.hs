{- |
   Module      : Pomc.Prob.FixPoint
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.FixPoint ( VarKey
                          , FixpEq(..)
                          , EqMap
                          , addFixpEq
                          , approxFixp
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          , preprocessApproxFixp
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)

import Data.Maybe (fromJust)
import Data.Ratio (approxRational)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT

import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV

import qualified Debug.Trace as DBG

type VarKey = (Int, Int)

data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving Show

type EqMap n = HT.BasicHashTable VarKey (FixpEq n)

-- EqMap containing only preprocessed live equations
data LiveEq n = PushLEq [(n, VarKey, VarKey)]
              | ShiftLEq [(n, VarKey)]
              deriving Show
type LEqSys n = IOVector (VarKey, LiveEq n)

type ProbVec n = HT.BasicHashTable VarKey n

addFixpEq :: MonadIO m => EqMap n -> VarKey -> FixpEq n -> m ()
addFixpEq eqMap varKey eq = liftIO $ HT.insert eqMap varKey eq

toLiveEqMap :: (MonadIO m, Fractional n) => EqMap n -> m (LEqSys n)
toLiveEqMap eqMap = liftIO $ do
  s <- stToIO $ BHT.size eqMap
  leqMap <- MV.unsafeNew s
  n <- HT.foldM
    (\i (k, eq) -> do
        case eq of
          PushEq terms -> MV.unsafeWrite leqMap i
                          (k, PushLEq $ map (\(p, k1, k2) -> (fromRational p, k1, k2)) terms)
                          >> return (i + 1)
          ShiftEq terms -> MV.unsafeWrite leqMap i
                           (k, ShiftLEq $ map (\(p, k1) -> (fromRational p, k1)) terms)
                           >> return (i + 1)
          _ -> return i
    ) 0 eqMap
  return $ MV.unsafeTake n leqMap

zeroVec :: (MonadIO m, Fractional n) => EqMap n -> m (ProbVec n)
zeroVec eqMap = liftIO $ do
  s <- stToIO $ BHT.size eqMap
  probVec <- HT.newSized s
  HT.mapM_ (\(k, eq) -> case eq of
               PopEq p -> HT.insert probVec k p
               _ -> HT.insert probVec k 0
           ) eqMap
  return probVec

evalEqSys :: (MonadIO m, Ord n, Fractional n)
          => LEqSys n -> n -> ProbVec n -> m Bool
evalEqSys leqMap eps probVec = liftIO $ MV.foldM' evalEq True leqMap where
  evalEq leqEps (key, eq) = do
    oldV <- fromJust <$> HT.lookup probVec key
    newV <- case eq of
      PushLEq terms -> sum <$> mapM
        (\(p, k1, k2) -> do
            v1 <- fromJust <$> HT.lookup probVec k1
            v2 <- fromJust <$> HT.lookup probVec k2
            return $ p * v1 * v2
        ) terms
      ShiftLEq terms -> sum <$> mapM (\(p, k) -> (p *) . fromJust <$> (HT.lookup probVec k)) terms
    HT.insert probVec key newV
    return $ leqEps && newV - oldV <= eps -- should be newV >= prevV -- TODO: use relative error

approxFixpFrom :: (MonadIO m, Ord n, Fractional n, Show n)
               => LEqSys n -> n -> Int -> ProbVec n -> m ()
approxFixpFrom leqMap eps maxIters probVec
  | maxIters <= 0 = return ()
  | otherwise = do
      lessThanEps <- evalEqSys leqMap eps probVec
      unless lessThanEps $ approxFixpFrom leqMap eps (maxIters - 1) probVec

-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
                      => EqMap n -> n -> Int -> m [VarKey]
preprocessApproxFixp eqMap eps maxIters = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMap eqMap
  -- iterate just one time and check if fixpoint remains zero
  approxFixpFrom leqMap eps maxIters probVec
  liftIO $ map fst . filter (\(_, p) -> p == 0) <$> HT.toList probVec

approxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
           => EqMap n -> n -> Int -> m (ProbVec n)
approxFixp eqMap eps maxIters = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMap eqMap
  approxFixpFrom leqMap eps maxIters probVec
  return probVec

defaultEps :: EqMapNumbersType
defaultEps = 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (MonadIO m, RealFrac n) => n -> ProbVec n -> m [(VarKey, Prob, n)]
toRationalProbVec eps probVec =
  liftIO $ map (\(k, p) -> (k, approxRational (p - eps) eps, p)) <$> HT.toList probVec
-- p - eps is to prevent approxRational from producing a result > p
