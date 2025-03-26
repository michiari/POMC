{-# LANGUAGE TupleSections #-}
-- {-# LANGUAGE DataKinds #-} -- For Rounded
{- |
   Module      : Pomc.Prob.OVI
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.OVI ( ovi
                     , OVISettings(..)
                     , defaultOVISettingsDouble
                     , defaultOVISettingsProb
                     -- , defaultOVISettingsRounded
                     , OVIResult(..)
                     , oviToRational
                     ) where

import Pomc.Prob.ProbUtils (Prob)
import Pomc.Prob.FixPoint
import Pomc.LogUtils (MonadLogger, logDebugN)

import Data.Ratio ((%), approxRational)
import Control.Monad.IO.Class (MonadIO())

import Witch.Instances (realFloatToRational)
import qualified Data.Vector as V

data OVISettings n = OVISettings { oviMaxIters :: Int
                                 , oviMaxKleeneIters :: Int
                                 , oviDampingFactor :: n
                                 , oviKleeneEps :: n
                                 , oviKleeneDampingFactor :: n
                                 , oviPowerIterEps :: n
                                 , oviPowerIterDampingFactor :: n
                                 , oviMaxPowerIters :: Int
                                 , oviRationalApproxEps :: n
                                 , oviMaxKIndIters :: Int
                                 }

defaultOVISettingsDouble :: OVISettings Double
defaultOVISettingsDouble = OVISettings
  { oviMaxIters = 50
  , oviMaxKleeneIters = 100000000
  , oviDampingFactor = 0.5
  , oviKleeneEps = 1e-4
  , oviKleeneDampingFactor = 1e-1
  , oviPowerIterEps = 1e-4
  , oviPowerIterDampingFactor = 1e-1
  , oviMaxPowerIters = 1000000
  , oviRationalApproxEps = 1e-8
  , oviMaxKIndIters = 50
  }

defaultOVISettingsProb :: OVISettings Prob
defaultOVISettingsProb = OVISettings
  { oviMaxIters = 10
  , oviMaxKleeneIters = 100000000
  , oviDampingFactor = 1 % 2
  , oviKleeneEps = 1 % 1000
  , oviKleeneDampingFactor = 1 % 10
  , oviPowerIterEps = 1 % 10000
  , oviPowerIterDampingFactor = 1 % 10
  , oviMaxPowerIters = 1000000
  , oviRationalApproxEps = 1 % 10^(8 :: Integer)
  , oviMaxKIndIters = 50
  }

-- defaultOVISettingsRounded :: OVISettings (R.Rounded 'R.TowardNearest 128)
-- defaultOVISettingsRounded = OVISettings
--   { oviMaxIters = 10
--   , oviMaxKleeneIters = 1000000
--   , oviDampingFactor = 0.5
--   , oviKleeneEps = 1e-3
--   , oviKleeneDampingFactor = 1e-1
--   , oviPowerIterEps = 1e-3
--   , oviPowerIterDampingFactor = 1e-1
--   , oviMaxPowerIters = 10000
--   , oviRationalApproxEps = 1e-8
--   , oviMaxKIndIters = 10
--   }

data OVIResult n = OVIResult { oviSuccess :: Bool
                             , oviIters :: Int
                             , oviLowerBound :: ProbVec n
                             , oviUpperBound :: ProbVec n
                             }

powerIterate :: (Fractional n, Ord n, Show n)
             => n -> Int -> PolyVector n -> ProbVec n -> (ProbVec n, n, Int)
powerIterate eps maxIters matrix oldEV =
  let go oldEigenVec eigenVal 0 = (oldEigenVec, eigenVal, 0)
      go oldEigenVec _ iters =
        let nnEigenVec = evalPolySys matrix oldEigenVec
            -- get approximate largest eigenvalue as the maxNorm
            eigenVal = V.maximum nnEigenVec
            -- normalize eigenVec on the largest eigenValue
            newEigenVec = V.map (/ eigenVal) nnEigenVec
            -- check absolute error
            stop = V.and (V.zipWith (\ov nv -> abs (ov - nv) <= eps) oldEigenVec newEigenVec)
        in if stop
          then (newEigenVec, eigenVal, iters)
          else go newEigenVec eigenVal (iters - 1)
  in go oldEV 0 maxIters

computeEigen :: (Fractional n, Ord n, Show n)
             =>  LEqSys n -> n -> Int -> ProbVec n -> ProbVec n -> (ProbVec n, n, Int)
computeEigen leqSys eps maxIters lowerApprox eigenVec =
  let matrix = jacobiTimesX leqSys lowerApprox
      (newEigenVec, eigenVal, iters) = powerIterate eps maxIters matrix eigenVec
  in (newEigenVec, eigenVal - 1, iters) -- -1 because we added the identity matrix

ovi :: (MonadIO m, MonadLogger m)
    => OVISettings Double -> AugEqMap k -> (k -> Double) -> ProbVec Double -> m (OVIResult Double)
ovi settings augEqMap f lowerApproxInitial = do
  -- create system containing only live equations
  leqSys <- toLiveEqMapWith augEqMap f
  logDebugN $ "Identified " ++ show (V.length leqSys) ++ " live variables..."
  let
    vecLength = V.length leqSys
    eigenVecInitial = V.replicate vecLength 1
    go _ _ lowerApprox upperApprox 0 _ = return OVIResult { oviSuccess  = False
                                , oviIters = oviMaxIters settings
                                , oviLowerBound = lowerApprox
                                , oviUpperBound = upperApprox
                                }
    go kleeneEps powerIterEps lowerApprox _ maxIters oldEigenVec = do
      let currentIter = oviMaxIters settings - maxIters
      logDebugN $ "Starting OVI iteration " ++ show currentIter

      let newLowerApprox = approxFixpFrom leqSys kleeneEps (oviMaxKleeneIters settings) lowerApprox
          (newEigenVec, eigenVal, iters) = computeEigen leqSys powerIterEps (oviMaxPowerIters settings)
                  newLowerApprox oldEigenVec
          debugMsg
            | iters == 0 = "Power Iteration exhausted!"
            | otherwise = concat
                [ "Power iteration converged after ", show ((oviMaxPowerIters settings) - iters)
                , " iterations. Eigenvalue: ", show eigenVal
                ]
          guessAndCheckInductive 0 = (False, V.empty)
          guessAndCheckInductive maxGuesses =
            let currentGuess = currentIter + 1 - maxGuesses
                scaleFactor = oviPowerIterEps settings *
                  (oviDampingFactor settings)^currentGuess
            -- upperApprox <- lowerApprox + eigenVal * scaleFactor
                newUpperApprox = V.zipWith (\eigenV l -> l + (eigenV * scaleFactor)) newEigenVec newLowerApprox

            -- check if upperApprox is inductive
                (inductive, _) = evalEqSys leqSys (<=) newUpperApprox
            in if inductive
                then (True, newUpperApprox)
                else guessAndCheckInductive (maxGuesses - 1)

          (inductive, newUpperApprox) = guessAndCheckInductive (currentIter + 1)
          adjustedUpperApprox = V.map (* 1.00001) newUpperApprox

      logDebugN debugMsg
      logDebugN $ "Finished iteration " ++ show currentIter ++ ". Inductive? "
        ++ show inductive
      if inductive
        then do
              logDebugN $ "Lower Approximation: " ++ show newLowerApprox
              logDebugN $ "EigenVector: " ++ show newEigenVec
              logDebugN $ "Upper Approximation: " ++ show adjustedUpperApprox
              return OVIResult { oviSuccess  = True
                         , oviIters = oviMaxIters settings - maxIters
                         , oviLowerBound = newLowerApprox
                         , oviUpperBound = adjustedUpperApprox
                         }
        else go
             (kleeneEps * oviKleeneDampingFactor settings)
             (powerIterEps * oviPowerIterDampingFactor settings)
             newLowerApprox
             adjustedUpperApprox
             (maxIters - 1)
             newEigenVec

  go (oviKleeneEps settings) (oviPowerIterEps settings) lowerApproxInitial lowerApproxInitial (oviMaxIters settings) eigenVecInitial

oviToRational :: (MonadIO m, MonadLogger m, Ord n, RealFrac n, Show n, RealFloat n)
                       => OVISettings n -> AugEqMap k -> (k -> n) -> OVIResult n -> m Bool
oviToRational settings augEqMap@(_, _) f oviRes = do
  let eps = oviRationalApproxEps settings
      -- two solutions for approximating the floating point upper bound with rational values
      f1 p = case realFloatToRational p of
        (Right v) -> v
        (Left exc) -> error $ "error when converting to rational upper bound " ++ show p ++ " - " ++ show exc
      f2eps p = approxRational (p + eps) eps

  rleqSys <- toLiveEqMapWith augEqMap (f1 . f)
  -- Convert upper bound to rational
  let initialRub1 = V.map f1 $ oviUpperBound oviRes
      initialRub2 = V.map f2eps $ oviUpperBound oviRes
      maxIters = oviMaxKIndIters settings
      checkWithKInd _ 0 = (False, maxIters)
      checkWithKInd rub kIters  =
        let
          -- Evaluate equation system
          (inductive, srub) = evalEqSys rleqSys (<=) rub
          newRub = V.zipWith min rub srub
        in if inductive
          then (inductive, maxIters - kIters + 1)
          else checkWithKInd newRub (kIters - 1)
      (successF1, itersF1) = checkWithKInd initialRub1 maxIters
      (successF2, itersF2) = checkWithKInd initialRub2 maxIters
  if successF1
    then do
      logDebugN $ unwords ["Successful k-induction with function realFloatToRational after", show itersF1, "iterations"]
      return successF1
    else do
      logDebugN $ unwords ["k-induction with function realFloatToRational failed in", show maxIters, "- Trying k-induction with function approxRational + eps."]
      logDebugN $ unwords ["Is k-induction with function approxRational + eps successful?", show successF2, "- Number of iterations:", show itersF2]
      return successF2

