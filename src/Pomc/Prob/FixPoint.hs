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
                          , zeroVec
                          , evalEqSys
                          , approxFixp
                          , defaultEps
                          , defaultBatch
                          , defaultMaxIters
                          , toRationalProbVec
                          ) where

import Pomc.Prob.ProbUtils (Prob)

import Data.Ratio (approxRational)
import Control.Monad.ST (RealWorld, stToIO)
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Data.HashTable.IO as HT

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HM

import qualified Debug.Trace as DBG

type VarKey = (Int, Int)

data FixpEq = PushEq [(Prob, VarKey, VarKey)]
            | ShiftEq [(Prob, VarKey)]
            | PopEq Prob
            | EndEq
            deriving Show

type EqMap = HT.BasicHashTable VarKey FixpEq

type EqSys = HashMap VarKey FixpEq
type ProbVec n = HashMap VarKey n

addFixpEq :: MonadIO m => EqMap -> VarKey -> FixpEq -> m ()
addFixpEq eqMap varKey eq = liftIO $ HT.insert eqMap varKey eq

toEqSys :: MonadIO m => EqMap -> m EqSys
toEqSys = liftIO . fmap HM.fromList . HT.toList

zeroVec :: Fractional n => EqSys -> ProbVec n
zeroVec eqSys = HM.map (const 0) eqSys

evalEqSys :: Fractional n => EqSys -> ProbVec n -> ProbVec n
evalEqSys eqSys probVec = HM.map evalEq eqSys
  where evalEq eq = case eq of
          PushEq terms -> sum
            $ map (\(p, v1, v2) -> fromRational p * (probVec HM.! v1) * (probVec HM.! v2)) terms
          ShiftEq terms -> sum $ map (\(p, v) -> fromRational p * (probVec HM.! v)) terms
          PopEq p -> fromRational p
          EndEq -> 1

approxFixpFrom :: (Ord n, Fractional n, Show n)
               => EqSys -> n -> Int -> Int -> ProbVec n -> ProbVec n
approxFixpFrom eqSys eps batch maxIters probVec
  | maxIters <= 0 = probVec
  | otherwise =
    let (newVec, prevVec) = -- TODO: try Gauss-Seidel update
          foldl (\(n, _) _ -> (evalEqSys eqSys n, n)) (probVec, probVec) [0..batch]
    in if all (<= eps) $ HM.unionWith (-) newVec prevVec -- should be newVec >= prevVec -- TODO: use relative error
       then newVec
       else DBG.traceShow newVec $ approxFixpFrom eqSys eps (min batch maxIters) (maxIters - batch) newVec

approxFixp :: (Ord n, Fractional n, Show n) => EqSys -> n -> Int -> Int -> ProbVec n
approxFixp eqSys eps batch maxIters = approxFixpFrom eqSys eps batch maxIters $ zeroVec eqSys

defaultEps :: Double
defaultEps = 1e-8

defaultBatch :: Int
defaultBatch = 100

defaultMaxIters :: Int
defaultMaxIters = 10000

toRationalProbVec :: (RealFrac n) => n -> ProbVec n -> ProbVec Prob
toRationalProbVec eps = HM.map (\p -> approxRational (p - eps) eps)
-- p - eps is to prevent approxRational from producing a result > p
