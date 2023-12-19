{- |
   Module      : Pomc.Prob.OVI
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.OVI (ovi) where

import Pomc.Prob.FixPoint
import Pomc.Prob.ProbUtils (Prob)

import Data.Maybe (fromJust)
import Control.Monad (forM)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT
import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV

data OVISettings n = OVISettings { oviMaxIters :: Int
                                 , oviMaxKleeneIters :: Int
                                 , oviKleeneEps :: n
                                 , oviKleeneDampingFactor :: n
                                 , oviPowerIterEps :: n
                                 , oviPowerIterDumpingFactor :: n
                                 , oviMaxPowerIters :: Int
                                 }

data OVIResult n = OVIResult { oviSuccess :: Bool
                             , oviIters :: Int
                             , oviUpperBound :: ProbVec n
                             }

data Monomial2 n = Quad n VarKey VarKey
                 | Lin n VarKey
                 | Const n
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
jacobiTimesX :: (MonadIO m, Num n) => LEqSys n -> ProbVec n -> m (PolyVector n)
jacobiTimesX leqSys v = liftIO $ do
  MV.generateM (MV.length leqSys)
    (\i -> do
        (k, eq) <- MV.read leqSys i
        poly <- case eq of
          PushLEq terms -> (Lin 1 k :) . concat <$> forM terms
            (\(p, k1, k2) -> do
                let pm = Quad p k1 k2
                coeff1 <- evalMonomial (monomialDerivative pm k1) v
                coeff2 <- evalMonomial (monomialDerivative pm k2) v
                return [Lin coeff1 k1, Lin coeff2 k2]
            )
          ShiftLEq terms -> (Lin 1 k :) <$> forM terms
            (\(p, k1) -> do
                coeff1 <- evalMonomial (monomialDerivative (Lin p k1) k1) v
                return $ Lin coeff1 k1
            )
        return (k, poly)
    )

powerIterate :: (MonadIO m, Num n) => n -> Int -> PolyVector n -> ProbVec n -> m n
powerIterate eps maxIters matrix eigenVec = error "TODO"

computeEigen :: (MonadIO m, Fractional n, Ord n)
             => LEqSys n -> n -> Int -> ProbVec n -> ProbVec n -> m n
computeEigen leqSys eps maxIters lowerApprox eigenVec = liftIO $ do
  matrix <- jacobiTimesX leqSys lowerApprox
  eigenVal <- powerIterate eps maxIters matrix eigenVec -- modifies eigenVec in-place
  maxNorm <- HT.foldM (\oldMax (_, v) -> return $ max oldMax v) 0 eigenVec
  -- normalize eigenVec on the maxNorm
  -- FIXME: iterate on leqSys because I don't know if I can modify a HT while iterating on it
  MV.mapM_ (\(k, _) -> HT.mutate eigenVec k (\(Just v) -> (Just $ v / maxNorm, v))) leqSys
  return $ eigenVal - 1 -- -1 because we added the identity matrix

ovi :: (MonadIO m, Fractional n, Ord n, Show n)
    => OVISettings n -> EqMap n -> ProbVec n -> m (OVIResult n)
ovi settings eqMap lowerApprox = liftIO $ do -- TODO: maybe make copy of lowerApprox?
  leqSys <- toLiveEqMap eqMap
  upperApprox <- HT.newSized =<< (stToIO $ BHT.size lowerApprox)
  eigenVec <- HT.newSized $ MV.length leqSys
  -- we only use live equations for eigenVec to avoid too many 0 values
  let
    go _ _ 0 = return OVIResult { oviSuccess  = False
                                , oviIters = oviMaxIters settings
                                , oviUpperBound = upperApprox
                                }
    go kleeneEps powerIterEps maxIters = do
      approxFixpFrom leqSys kleeneEps (oviMaxKleeneIters settings) lowerApprox
      eigenVal <- computeEigen leqSys powerIterEps (oviMaxPowerIters settings)
                  lowerApprox eigenVec -- modifies eigenVec

      -- upperApprox <- lowerApprox + eigenVal
      HT.mapM_
        (\(k, l) -> do
            eigenV <- fromJust <$> HT.lookup eigenVec k
            HT.insert upperApprox k (l + eigenV)
        )
        lowerApprox

      -- TODO: add k-induction with scaling factor
      -- check if upperApprox is inductive
      inductive <- evalEqSys leqSys (\prev newV oldV -> prev && newV <= oldV) upperApprox

      if inductive
        then return OVIResult { oviSuccess  = True
                              , oviIters = oviMaxIters settings - maxIters
                              , oviUpperBound = upperApprox
                              } -- This is the upperApprox iterated once: is this ok?
        else go
             (kleeneEps * oviKleeneDampingFactor settings)
             (powerIterEps * oviPowerIterDumpingFactor settings)
             (maxIters - 1)

  go (oviKleeneEps settings) (oviPowerIterEps settings) (oviMaxIters settings)

