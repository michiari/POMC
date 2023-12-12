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
                          , toEqSys
                          , evalEqSys
                          , approxFixp
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          ) where

import Pomc.Prob.ProbUtils (Prob)

import Data.Maybe (fromJust)
import Data.Ratio (approxRational)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT

import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MV

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HM

import qualified Debug.Trace as DBG

type VarKey = (Int, Int)

data FixpEq = PushEq [(Prob, VarKey, VarKey)]
            | ShiftEq [(Prob, VarKey)]
            | PopEq Prob
            deriving Show

type EqMap = HT.BasicHashTable VarKey FixpEq

type EqSys = HashMap VarKey FixpEq
type ProbVec n = HT.BasicHashTable VarKey n

addFixpEq :: MonadIO m => EqMap -> VarKey -> FixpEq -> m ()
addFixpEq eqMap varKey eq = liftIO $ HT.insert eqMap varKey eq

toEqSys :: MonadIO m => EqMap -> m EqSys
toEqSys = liftIO . fmap HM.fromList . HT.toList

zeroVec :: (MonadIO m, Num n) => EqMap -> m (ProbVec n)
zeroVec eqMap = liftIO $ do
  s <- stToIO $ BHT.size eqMap
  probVec <- HT.newSized s
  HT.mapM_ (\(k, _) -> HT.insert probVec k 0) eqMap
  return probVec

evalEqSys :: (MonadIO m, Ord n, Fractional n) => EqMap -> n -> ProbVec n -> m Bool
evalEqSys eqMap eps probVec = liftIO $ HT.foldM evalEq True eqMap where
  evalEq leqEps (key, eq) = do
    oldV <- fromJust <$> HT.lookup probVec key
    newV <- case eq of
      PushEq terms -> sum <$> mapM
        (\(p, k1, k2) -> do
            v1 <- fromJust <$> HT.lookup probVec k1
            v2 <- fromJust <$> HT.lookup probVec k2
            return $ fromRational p * v1 * v2 -- TODO: preprocess eqMap so that p is already double
        ) terms
      ShiftEq terms -> sum <$> mapM (\(p, k) -> (fromRational p *) . fromJust <$> (HT.lookup probVec k)) terms
      PopEq p -> return $ fromRational p
    HT.insert probVec key newV
    return $ leqEps && newV - oldV <= eps -- should be newV >= prevV -- TODO: use relative error

approxFixpFrom :: (MonadIO m, Ord n, Fractional n, Show n)
               => EqMap -> n -> Int -> ProbVec n -> m ()
approxFixpFrom eqMap eps maxIters probVec
  | maxIters <= 0 = return ()
  | otherwise = do
      lessThanEps <- evalEqSys eqMap eps probVec
      unless lessThanEps $ approxFixpFrom eqMap eps (maxIters - 1) probVec

approxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
           => EqMap -> n -> Int -> m (ProbVec n)
approxFixp eqMap eps maxIters = do
  probVec <- zeroVec eqMap
  approxFixpFrom eqMap eps maxIters probVec
  return probVec

defaultEps :: Double
defaultEps = 1e-8

defaultMaxIters :: Int
defaultMaxIters = 10000

toRationalProbVec :: (MonadIO m, RealFrac n) => n -> ProbVec n -> m [(VarKey, Prob)]
toRationalProbVec eps probVec =
  liftIO $ map (\(k, p) -> (k, approxRational (p - eps) eps)) <$> HT.toList probVec
-- p - eps is to prevent approxRational from producing a result > p
