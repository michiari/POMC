{- |
   Module      : Pomc.Prob.OVI
   Copyright   : 2023-2026 Michele Chiari, Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.OVI ( ovi
                     , OVISettings(..)
                     , defaultOVISettingsDouble
                     -- , defaultOVISettingsProb
                     -- , defaultOVISettingsRounded
                     , OVIResult(..)
                     , oviToRational
                     ) where

import Pomc.Prob.FixPoint
import Pomc.LogUtils (MonadLogger, logDebugN)
import Pomc.Prob.ProbUtils (defaultMaxIters, defaultEps)

import Data.Ratio (approxRational)
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

defaultOVISettingsDouble :: Double -> OVISettings Double
defaultOVISettingsDouble eps = OVISettings
  { oviMaxIters = 50
  , oviMaxKleeneIters = 100000000
  , oviDampingFactor = 0.5
  , oviKleeneEps = eps
  , oviKleeneDampingFactor = 1e-1
  , oviPowerIterEps = 10 * eps
  , oviPowerIterDampingFactor = 1e-1
  , oviMaxPowerIters = 1000000
  , oviRationalApproxEps = defaultEps
  , oviMaxKIndIters = 50
  }

--  defaultOVISettingsProb :: OVISettings Prob
--  defaultOVISettingsProb = OVISettings
--    { oviMaxIters = 10
--    , oviMaxKleeneIters = 100000000
--    , oviDampingFactor = 1 % 2
--    , oviKleeneEps = defaultREps
--    , oviKleeneDampingFactor = 1 % 10
--    , oviPowerIterEps = defaultREps
--    , oviPowerIterDampingFactor = 1 % 10
--    , oviMaxPowerIters = 1000000
--    , oviRationalApproxEps = 1 % 10^(8 :: Integer)
--    , oviMaxKIndIters = 50
--    }

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
                             , oviLowerBound :: ProbVec n -- note that this is the lower bound computed with upper bounds coefficients
                             , oviUpperBound :: ProbVec n
                             }

powerIterate :: (Fractional n, Ord n, Show n)
             => n -> Int -> PolyVector n -> ProbVec n -> (ProbVec n, n, Int)
powerIterate eps maxIters matrix oldEV =
  let go oldEigenVec eigenVal 0 = (oldEigenVec, eigenVal, 0)
      go oldEigenVec _ iters =
        let nnEigenVec = evalPolySys matrix oldEigenVec
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
    => OVISettings Double -> LEqSys Double -> ProbVec Double -> m (OVIResult Double)
ovi settings leqSys lowerApproxInitial = do
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

      -- computing eigenvector and eigenvalue
      let newLowerApprox = approxFixpFrom leqSys kleeneEps (oviMaxKleeneIters settings) lowerApprox
          (newEigenVec, eigenVal, iters) = computeEigen leqSys powerIterEps (oviMaxPowerIters settings)
                  newLowerApprox oldEigenVec
          debugMsg
            | iters == 0 = "Power Iteration exhausted!"
            | otherwise = concat
                [ "Power iteration converged after ", show ((oviMaxPowerIters settings) - iters)
                , " iterations. Eigenvalue: ", show eigenVal
                ]
      logDebugN debugMsg
      -- guessing an inductive upper bound
      let guessAndCheckInductive 0 = (False, newLowerApprox)
          guessAndCheckInductive maxGuesses =
            let currentGuess = currentIter + 1 - maxGuesses
                scaleFactor = oviPowerIterEps settings *
                  (oviDampingFactor settings)^currentGuess
            -- upperApprox <- lowerApprox + eigenVal * scaleFactor
                candidateUpperApprox = V.zipWith (\eigenV l -> l + (eigenV * scaleFactor))
                  newEigenVec newLowerApprox

            -- check if upperApprox is inductive
                (induct, _) = evalEqSys leqSys (<=) candidateUpperApprox
            in if induct
                then (True, candidateUpperApprox)
                else guessAndCheckInductive (maxGuesses - 1)

          (inductive, upperApprox) = guessAndCheckInductive (currentIter + 1)
          adjustedUpperApprox = approxFixpFromAbove leqSys kleeneEps defaultMaxIters upperApprox
      logDebugN $ "Finished iteration " ++ show currentIter ++ ". Inductive? "
        ++ show inductive
      if inductive
        then do
              logDebugN $ "Refined lower Approximation: " ++ show newLowerApprox
              --logDebugN $ "EigenVector: " ++ show newEigenVec
              logDebugN $ "Computed Upper Approximation: " ++ show adjustedUpperApprox
              return OVIResult { oviSuccess  = True
                         , oviIters = currentIter
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
  go (oviKleeneEps settings) (oviPowerIterEps settings)
    lowerApproxInitial lowerApproxInitial (oviMaxIters settings) eigenVecInitial

oviToRational :: (MonadIO m, MonadLogger m, Ord n, RealFrac n, Show n, RealFloat n, Show n)
  => OVISettings n -> LEqSys n -> OVIResult n -> m Bool
oviToRational settings leqSys oviRes = do
  let rationalEps = oviRationalApproxEps settings
      -- two solutions for approximating the floating point upper bound with rational values
      f1 p = case realFloatToRational p of
        (Right v) -> v
        (Left exc) -> error $ "error when converting to rational upper bound " ++ show p ++ " - " ++ show exc
      f2eps p = approxRational (p + rationalEps) rationalEps
      rleqSys :: LEqSys Rational
      rleqSys = V.map (fmap f1) leqSys

  -- Convert upper bound to rational
      initialRub1 = V.map f1 $ oviUpperBound oviRes
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
