-- {-# LANGUAGE DataKinds #-} -- For Rounded
{- |
   Module      : Pomc.Prob.OVI
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.OVI ( oviWithHints
                     , OVISettings(..)
                     , defaultOVISettingsDouble
                     , defaultOVISettingsProb
                     -- , defaultOVISettingsRounded
                     , OVIResult(..)
                     , oviToRationalWithHints
                     ) where

import Pomc.Prob.ProbUtils (Prob)
import Pomc.Prob.FixPoint

import Data.Ratio ((%), approxRational)
import Data.Maybe (fromJust, isJust)
import Control.Monad (forM, when)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT
import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV
-- import qualified Numeric.Rounded as R

import Witch.Instances (realFloatToRational)

import qualified Debug.Trace as DBG

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
  , oviMaxKleeneIters = 1000000
  , oviDampingFactor = 0.5
  , oviKleeneEps = 1e-3
  , oviKleeneDampingFactor = 1e-1
  , oviPowerIterEps = 1e-3
  , oviPowerIterDampingFactor = 1e-1
  , oviMaxPowerIters = 10000
  , oviRationalApproxEps = 1e-8
  , oviMaxKIndIters = 10
  }

defaultOVISettingsProb :: OVISettings Prob
defaultOVISettingsProb = OVISettings
  { oviMaxIters = 10
  , oviMaxKleeneIters = 1000000
  , oviDampingFactor = 1 % 2
  , oviKleeneEps = 1 % 1000
  , oviKleeneDampingFactor = 1 % 10
  , oviPowerIterEps = 1 % 1000
  , oviPowerIterDampingFactor = 1 % 10
  , oviMaxPowerIters = 10000
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
                             , oviUpperBound :: ProbVec n
                             }

data Monomial2 n = Quad n VarKey VarKey
                 | Lin n VarKey
                 | Const n
                 deriving Show
type Polynomial2 n = [Monomial2 n]
type PolyVector n = IOVector (VarKey, Polynomial2 n)

evalMonomial :: (MonadIO m, Num n) => Monomial2 n -> ProbVec n -> m n
evalMonomial m v = liftIO $ case m of
  Quad c k1 k2 -> do
    v1 <- fromJust <$> HT.lookup v k1
    v2 <- fromJust <$> HT.lookup v k2
    return $ c * v1 * v2
  Lin c k1 -> do
    v1 <- fromJust <$> HT.lookup v k1
    return $ c * v1
  Const c -> return c

evalPolynomial :: (MonadIO m, Num n) => Polynomial2 n -> ProbVec n -> m n
evalPolynomial p v = liftIO $ sum <$> mapM (flip evalMonomial v) p

evalPolySys :: (MonadIO m, Ord n, Fractional n)
            => PolyVector n -> (Bool -> n -> n -> Bool) -> ProbVec n -> ProbVec n
            -> m Bool
evalPolySys polySys checkRes src dst = liftIO $ MV.foldM' eval True polySys
  where eval prevCheck (key, poly) = do
          oldV <- fromJust <$> HT.lookup src key
          newV <- evalPolynomial poly src
          HT.insert dst key newV
          return $ checkRes prevCheck newV oldV

-- compute dm/dx
monomialDerivative :: Num n => Monomial2 n -> VarKey -> Monomial2 n
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
jacobiTimesX :: (MonadIO m, Num n) => LEqSys n -> ProbVec n -> ProbVec n -> m (PolyVector n)
jacobiTimesX leqSys v checkVec = liftIO $ MV.generateM (MV.length leqSys)
  -- checkVec is just to check that a variable is alive in O(1)
  (\i -> do
        (k, eq) <- MV.read leqSys i
        poly <- case eq of
          PushLEq terms -> (Lin 1 k :) . concat <$> forM terms
            (\(p, k1, k2) -> do
                let pm = Quad p k1 k2
                m1 <- jtxMonomial pm k1
                m2 <- jtxMonomial pm k2
                return $ m1 ++ m2
            )
          ShiftLEq terms -> (Lin 1 k :) . concat <$> forM terms
            (\(p, k1) -> jtxMonomial (Lin p k1) k1)
        return (k, poly)
    )
  where jtxMonomial lmon key = do
          check <- HT.lookup checkVec key
          if isJust check
            then do
            coeff <- evalMonomial (monomialDerivative lmon key) v
            return [Lin coeff key]
            else return []

powerIterate :: (MonadIO m, Fractional n, Ord n, Show n)
             => n -> Int -> PolyVector n -> ProbVec n -> m n
powerIterate eps maxIters matrix eigenVec = do
  oldEigenVec <- copyVec eigenVec
  let go eigenVal 0 = DBG.traceM "Power iterations exhausted!" >> return eigenVal
      go _ iters = do
        _ <- evalPolySys matrix (\p _ _ -> p) oldEigenVec eigenVec
        -- get approximate largest eigenvalue as the maxNorm
        eigenVal <- HT.foldM (\oldMax (_, v) -> return $ max oldMax v) 0 eigenVec
        -- normalize eigenVec on the largest eigenValue
        -- FIXME: iterate on matrix because I don't know if I can modify a HT while iterating on it
        MV.mapM_ (\(k, _) -> HT.mutate eigenVec k (\(Just v) -> (Just $ v / eigenVal, v))) matrix
        -- check absolute error
        stop <- HT.foldM (\chk (k, nv) -> do
                             ov <- fromJust <$> HT.lookup oldEigenVec k
                             return $ chk && abs (ov - nv) <= eps
                         ) True eigenVec
        if stop
          then DBG.traceM ("Power iteration converged after " ++ show (maxIters - iters) ++ " iterations. Eigenvalue: " ++ show eigenVal)
               >> return eigenVal
          else do
          HT.mapM_ (\(k, v) -> HT.insert oldEigenVec k v) eigenVec
          go eigenVal (iters - 1)
  liftIO $ go 0 maxIters


computeEigen :: (MonadIO m, Fractional n, Ord n, Show n)
             => LEqSys n -> n -> Int -> ProbVec n -> ProbVec n -> m n
computeEigen leqSys eps maxIters lowerApprox eigenVec = liftIO $ do
  matrix <- jacobiTimesX leqSys lowerApprox eigenVec
  --DBG.traceShowM =<< V.freeze matrix
  eigenVal <- powerIterate eps maxIters matrix eigenVec -- modifies eigenVec in-place
  return $ eigenVal - 1 -- -1 because we added the identity matrix


oviWithHints :: (MonadIO m, Fractional n, Ord n, Show n)
    => OVISettings n -> EqMap n -> [(Int,Int)] -> m (OVIResult n)
oviWithHints settings eqMap lVars = liftIO $ do
  s <- stToIO $ BHT.size eqMap
  DBG.traceM $ "Starting OVI on a system with " ++ show s ++ " variables..."
  lowerApprox <- zeroVec eqMap
  -- initialize upperApprox with lowerApprox, so we copy non-alive variable values
  upperApprox <- copyVec lowerApprox
  evalUpperApprox <- newVecSameSize lowerApprox
  -- create system containing only live equations
  leqSys <- toLiveEqMapWithHints eqMap lVars
  -- create eigenVec and initialize it to 1
  -- we only use live equations for eigenVec to avoid too many 0 values
  eigenVec <- HT.newSized $ MV.length leqSys
  MV.forM_ leqSys (\(k, _) -> HT.insert eigenVec k 1)
  let
    go _ _ 0 = return OVIResult { oviSuccess  = False
                                , oviIters = oviMaxIters settings
                                , oviLowerBound = lowerApprox
                                , oviUpperBound = upperApprox
                                }
    go kleeneEps powerIterEps maxIters = do
      let currentIter = oviMaxIters settings - maxIters
      DBG.traceM $ "Starting OVI iteration " ++ show currentIter

      approxFixpFrom leqSys kleeneEps (oviMaxKleeneIters settings) lowerApprox
      -- DBG.traceShowM =<< (liftIO $ HT.toList lowerApprox)
      eigenVal <- computeEigen leqSys powerIterEps (oviMaxPowerIters settings)
                  lowerApprox eigenVec -- modifies eigenVec
      DBG.traceM $ "The eigenvalue is " ++ show eigenVal

      let guessAndCheckInductive 0 = return False
          guessAndCheckInductive maxGuesses = do
            let currentGuess = currentIter + 1 - maxGuesses
                scaleFactor = oviPowerIterEps settings *
                  (oviDampingFactor settings)^currentGuess
            -- upperApprox <- lowerApprox + eigenVal * scaleFactor
            HT.mapM_
              (\(k, l) -> do
                  maybeEigenV <- HT.lookup eigenVec k
                  when (isJust maybeEigenV) $
                    HT.insert upperApprox k (l + (fromJust maybeEigenV * scaleFactor))
              )
              lowerApprox

            -- check if upperApprox is inductive
            let check prev newV oldV = prev && newV <= oldV
                  -- prev && 1 / (oldV - newV) >= 0
                  -- prev && (1-eps)*newV + eps <= oldV
            inductive <- evalEqSys leqSys check upperApprox evalUpperApprox
            DBG.traceM $ "Is guess " ++ show currentGuess ++ " inductive? " ++ show inductive
            if inductive
              then return True
              else guessAndCheckInductive (maxGuesses - 1)
      inductive <- guessAndCheckInductive (currentIter + 1)

      DBG.traceM $ "Finished iteration " ++ show currentIter ++ ". Inductive? "
        ++ show inductive
      if inductive
        then do
        MV.forM_ leqSys (\(k, _) -> HT.mutate upperApprox k (\(Just v) -> (Just $ v * 1.00001, v)))
        return OVIResult { oviSuccess  = True
                         , oviIters = oviMaxIters settings - maxIters
                         , oviLowerBound = lowerApprox
                         , oviUpperBound = upperApprox
                         }
        else go
             (kleeneEps * oviKleeneDampingFactor settings)
             (powerIterEps * oviPowerIterDampingFactor settings)
             (maxIters - 1)

  go (oviKleeneEps settings) (oviPowerIterEps settings) (oviMaxIters settings)

oviToRationalWithHints :: (MonadIO m, Ord n, RealFrac n, Show n, RealFloat n)
              => OVISettings n -> EqMap n -> OVIResult n -> [(Int,Int)] -> m Bool
oviToRationalWithHints settings eqMap oviRes lVars = liftIO $ do
  let eps = oviRationalApproxEps settings
      fracEps = toRational eps
      -- two solutions for approximating the floating point upper bound with rational values
      f1 p = case realFloatToRational p of 
        (Right v) -> v
        (Left exc) -> error $ "error when converting to rational upper bound " ++ show p ++ " - " ++ show exc
      f2 p = approxRational p eps
      f2eps p = approxRational (p + eps) eps
      showF1 = "realFloatToRational"
      showF2 = "approxRational"

  reqMap <- mapEqMapPop f1 eqMap
  rleqSys <- toLiveEqMapWithHints reqMap lVars
  -- Convert upper bound to rational
  rub <- mapVec f1 $ oviUpperBound oviRes
  srub <- HT.newSized =<< stToIO (BHT.size rub)
  let checkWithKInd _ _ _  0 = return False
      checkWithKInd showF rleqSys srub kIters  = do
        -- Evaluate equation system
        inductive <- evalEqSys rleqSys (\prev newV oldV -> prev && newV <= oldV) rub srub

        DBG.traceM $ "Is the rational approximation inductive? " ++ show inductive
        if inductive
          then return inductive
          else do
          DBG.traceM $ "Trying with k-induction with function " ++ showF  ++ ", remaining iterations: " ++ show kIters
          HT.mapM_ (\(k, sv) -> do
                       v <- fromJust <$> HT.lookup rub k
                       HT.insert rub k (min v sv) 
                   ) srub
          checkWithKInd showF rleqSys srub (kIters - 1) 
  success <- checkWithKInd showF1 rleqSys srub $ oviMaxKIndIters settings
  if success 
    then return success
    else do 
      reqMap <- mapEqMapPop f2 eqMap
      rleqSys <- toLiveEqMapWithHints reqMap lVars
      -- Convert upper bound to rational
      rub <- mapVec f2eps $ oviUpperBound oviRes
      srub <- HT.newSized =<< stToIO (BHT.size rub)
      checkWithKInd showF2 rleqSys srub $ oviMaxKIndIters settings

