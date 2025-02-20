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
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (readIORef)

import Witch.Instances (realFloatToRational)
import Data.Either (isLeft)

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Set as Set

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
  { oviMaxIters = 20
  , oviMaxKleeneIters = 100000000
  , oviDampingFactor = 0.5
  , oviKleeneEps = 1e-4
  , oviKleeneDampingFactor = 1e-1
  , oviPowerIterEps = 1e-4
  , oviPowerIterDampingFactor = 1e-1
  , oviMaxPowerIters = 1000000
  , oviRationalApproxEps = 1e-8
  , oviMaxKIndIters = 10
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
  , oviMaxKIndIters = 10
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
                             , oviUpperBound :: ProbVec (VarKey, n)
                             }

-- Int values are variables' indexes in the current src 
-- n are constant coefficients
data Monomial2 n = Quad n Int Int
                 | Lin n Int
                 | Const n
                 deriving Show
type Polynomial2 n = [Monomial2 n]
type PolyVector n = Vector (Polynomial2 n)

evalMonomial :: (Num n) => ProbVec n -> Monomial2 n -> n
evalMonomial v m = case m of
  Quad c k1 k2 -> c * (v V.! k1) * (v V.! k2)
  Lin c k1 -> c * (v V.! k1)
  Const c -> c

evalPolynomial :: (Num n) => Polynomial2 n -> ProbVec n -> n
evalPolynomial p v = sum . map (evalMonomial v) $ p

evalPolySys :: (Ord n, Fractional n) => PolyVector n -> ProbVec n -> ProbVec n
evalPolySys polySys src = V.map (`evalPolynomial` src) polySys

-- compute dm/dx
monomialDerivative :: Num n => Monomial2 n -> Int -> Monomial2 n
monomialDerivative m x = case m of -- ugly but it works
  Quad c k1 k2 | k1 == k2 && k2 == x -> Lin (2 * c) x -- square
               | k1 == x -> Lin c k2
               | k2 == x -> Lin c k1
               | otherwise -> Const 0
  Lin c k | k == x -> Const c
          | otherwise -> Const 0
  Const _ -> Const 0

-- compute (J|v + I) x, where J|v is the Jacobian of leqSys evaluated on v,
-- I is the identity matrix, and x is the vector of all variables
jacobiTimesX :: (Num n) => AugEqMap n -> LEqSys n -> ProbVec n -> PolyVector n
jacobiTimesX (_, _) leqSys v =
  let jtxMonomial lmon (Left key) = [Lin coeff key]
        where coeff = evalMonomial v (monomialDerivative lmon key)
      jtxMonomial _ _ = []

      constructPoly k (PushLEq terms) = (Lin 1 k :) . concatMap
        (\(p, k1, k2) ->
            let build (Left k1)   (Left k2) = Quad p k1 k2
                build (Left k1)   (Right val) = Lin (p * val) k1
                build (Right val) (Left k1)  = Lin (p * val) k1
                build _ _ = error "unexpected"
                pm = build k1 k2
                m1 = jtxMonomial pm k1
                m2 = jtxMonomial pm k2
            in  m1 ++ m2
        ) $ filter (\(_, eitherK1, eitherK2) -> isLeft eitherK1 || isLeft eitherK2) terms
      constructPoly k (ShiftLEq terms) = (Lin 1 k :) . concatMap
        (\(p, Left k1) -> jtxMonomial (Lin p k1) (Left k1))
        $ filter (\(_, eitherP) -> isLeft eitherP) terms
        
  in V.imap constructPoly leqSys

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
            stop = V.all (\(ov, nv) -> abs (ov - nv) <= eps) (V.zip oldEigenVec newEigenVec)
        in if stop
          then (newEigenVec, eigenVal, iters)
          else go newEigenVec eigenVal (iters - 1)
  in go oldEV 0 maxIters

computeEigen :: (Fractional n, Ord n, Show n)
             => AugEqMap n -> LEqSys n -> n -> Int -> ProbVec n -> ProbVec n -> (ProbVec n, n, Int)
computeEigen augEqMap leqSys eps maxIters lowerApprox eigenVec =
  let matrix = jacobiTimesX augEqMap leqSys lowerApprox
      (newEigenVec, eigenVal, iters) = powerIterate eps maxIters matrix eigenVec
  in (newEigenVec, eigenVal - 1, iters) -- -1 because we added the identity matrix

ovi :: (MonadIO m, MonadLogger m, Fractional n, Ord n, Show n, Num n)
    => OVISettings n -> AugEqMap n -> m (OVIResult n)
ovi settings augEqMap@(_, lVarsRef) = do

  -- create system containing only live equations
  leqSys <- toLiveEqMap augEqMap
  logDebugN $ "Identified " ++ show (V.length leqSys) ++ " live variables..."
  lVars <- liftIO $ readIORef lVarsRef
  let
    varsVec = V.fromList . Set.toList $ lVars
    vecLength = V.length varsVec
    lowerApproxInitial = V.replicate vecLength 0
    upperApproxInitial = V.map (,0) varsVec
    eigenVecInitial = V.replicate vecLength 1
    go _ _ lowerApprox upperApprox 0 _ = return OVIResult { oviSuccess  = False
                                , oviIters = oviMaxIters settings
                                , oviLowerBound = lowerApprox
                                , oviUpperBound = upperApprox
                                }
    go kleeneEps powerIterEps lowerApprox _ maxIters oldEigenVec = do
      let currentIter = oviMaxIters settings - maxIters
      logDebugN $ "Starting OVI iteration " ++ show currentIter

      let newLowerApprox = approxFixpFrom augEqMap leqSys kleeneEps (oviMaxKleeneIters settings) lowerApprox
          (newEigenVec, eigenVal, iters) = computeEigen augEqMap leqSys powerIterEps (oviMaxPowerIters settings)
                  newLowerApprox oldEigenVec -- modifies eigenVec
          debugMsg 
            | iters == 0 = "Power Iteration exhausted!"
            | otherwise = concat
                [ "Power iteration converged after ", show ((oviMaxPowerIters settings) - iters)
                , " iterations. Eigenvalue: ", show eigenVal
                ]

          guessAndCheckInductive 0 = return (False, V.empty)
          guessAndCheckInductive maxGuesses = do
            let currentGuess = currentIter + 1 - maxGuesses
                scaleFactor = oviPowerIterEps settings *
                  (oviDampingFactor settings)^currentGuess
            -- upperApprox <- lowerApprox + eigenVal * scaleFactor
                newUpperApprox = V.map (\(eigenV, l) -> l + (eigenV * scaleFactor)) (V.zip newEigenVec newLowerApprox)

            -- check if upperApprox is inductive
                check newV oldV = newV <= oldV
                  -- prev && 1 / (oldV - newV) >= 0
                  -- prev && (1-eps)*newV + eps <= oldV
                (inductive, _) = evalEqSys leqSys check newUpperApprox
            logDebugN $ "Is guess " ++ show currentGuess ++ " inductive? " ++ show inductive
            if inductive
              then return (True, newUpperApprox)
              else guessAndCheckInductive (maxGuesses - 1)
              
      logDebugN $ "Lower Approximation: " ++ show newLowerApprox
      logDebugN debugMsg
      logDebugN $ "EigenVector: " ++ show newEigenVec
      (inductive, newUpperApprox) <- guessAndCheckInductive (currentIter + 1)
      let upperApproxWithKeys = V.zip varsVec . V.map (* 1.00001) $ newUpperApprox

      logDebugN $ "Finished iteration " ++ show currentIter ++ ". Inductive? "
        ++ show inductive

      if inductive
        then return OVIResult { oviSuccess  = True
                         , oviIters = oviMaxIters settings - maxIters
                         , oviLowerBound = newLowerApprox
                         , oviUpperBound = upperApproxWithKeys
                         }
        else go
             (kleeneEps * oviKleeneDampingFactor settings)
             (powerIterEps * oviPowerIterDampingFactor settings)
             newLowerApprox
             upperApproxWithKeys
             (maxIters - 1)
             newEigenVec

  go (oviKleeneEps settings) (oviPowerIterEps settings) lowerApproxInitial upperApproxInitial (oviMaxIters settings) eigenVecInitial

oviToRational :: (MonadIO m, MonadLogger m, Ord n, RealFrac n, Show n, RealFloat n)
                       => OVISettings n -> AugEqMap n -> OVIResult n -> m Bool
oviToRational settings augEqMap@(_, _) oviRes = do
  let eps = oviRationalApproxEps settings
      -- two solutions for approximating the floating point upper bound with rational values
      f1 p = case realFloatToRational p of
        (Right v) -> v
        (Left exc) -> error $ "error when converting to rational upper bound " ++ show p ++ " - " ++ show exc
      f2eps p = approxRational (p + eps) eps
      showF1 = "realFloatToRational"
      showF2 = "approxRational + eps"

  rleqSys <- toLiveEqMapWith augEqMap f1
  -- Convert upper bound to rational
  let initialRub1 = V.map (\(_, v) -> f1 v) $ oviUpperBound oviRes
      initialRub2 = V.map (\(_, v) -> f2eps v) $ oviUpperBound oviRes
      checkWithKInd _ _ 0 = return False
      checkWithKInd showF rub kIters  = do
        -- Evaluate equation system
        let (inductive, srub) = evalEqSys rleqSys (<=) rub

        logDebugN $ "Is the rational approximation inductive? " ++ show inductive
        if inductive
          then return inductive
          else do
            logDebugN $ "Trying with k-induction with function " ++ showF  ++ ", remaining iterations: " ++ show kIters
            let newRub = V.map (uncurry min) (V.zip rub srub)
            checkWithKInd showF newRub (kIters - 1)
  success <- checkWithKInd showF1 initialRub1 $ oviMaxKIndIters settings
  if success
    then return success
    else checkWithKInd showF2 initialRub2 $ oviMaxKIndIters settings
