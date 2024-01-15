{- |
   Module      : Pomc.Prob.FixPoint
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.FixPoint ( VarKey
                          , FixpEq(..)
                          , EqMap
                          , LiveEq(..)
                          , LEqSys
                          , ProbVec
                          , mapEqMapPop
                          , addFixpEq
                          , toLiveEqMap
                          , newVecSameSize
                          , mapVec
                          , copyVec
                          , zeroVec
                          , evalEqSys
                          , numLiveEqSys
                          , approxFixpFrom
                          , approxFixp
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          , toUpperRationalProbVec
                          , preprocessApproxFixp
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)

import Data.Maybe (fromJust, isJust)
import Data.Ratio (approxRational)
import Control.Monad (unless, filterM, when)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT

import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV

import Data.Ratio((%))

import qualified Debug.Trace as DBG
import Control.Monad (foldM)

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

mapEqMapPop :: MonadIO m => (a -> b) -> EqMap a -> m (EqMap b)
mapEqMapPop f eqMap = liftIO $ do
  newMap <- HT.newSized =<< stToIO (BHT.size eqMap)
  let go (k, PopEq p) = HT.insert newMap k $ PopEq (f p)
      go (k, PushEq terms) = HT.insert newMap k $ PushEq terms
      go (k, ShiftEq terms) = HT.insert newMap k $ ShiftEq terms
  HT.mapM_ go eqMap
  return newMap

addFixpEq :: MonadIO m => EqMap n -> VarKey -> FixpEq n -> m ()
addFixpEq eqMap varKey eq = liftIO $ HT.insert eqMap varKey eq

substituteKnownVals :: MonadIO m => EqMap n -> ProbVec n -> m ()
substituteKnownVals eqMap knownVals =
  liftIO $ HT.mapM_ (\(k, v) -> HT.insert eqMap k $ PopEq v) knownVals

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

newVecSameSize :: MonadIO m => ProbVec a -> m (ProbVec b)
newVecSameSize vec = liftIO $ HT.newSized =<< stToIO (BHT.size vec)

mapVec :: MonadIO m => (a -> b) -> ProbVec a -> m (ProbVec b)
mapVec f vec = liftIO $ do
  newVec <- HT.newSized =<< stToIO (BHT.size vec)
  HT.mapM_ (\(k, v) -> HT.insert newVec k $ f v) vec
  return newVec

copyVec :: MonadIO m => ProbVec n -> m (ProbVec n)
copyVec = mapVec id

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
          => LEqSys n -> (Bool -> n -> n -> Bool) -> ProbVec n -> ProbVec n -> m Bool
evalEqSys leqMap checkRes src dst = liftIO $ MV.foldM' evalEq True leqMap where
  evalEq prevCheck (key, eq) = do
    oldV <- fromJust <$> HT.lookup src key
    newV <- case eq of
      PushLEq terms -> sum <$> mapM
        (\(p, k1, k2) -> do
            v1 <- fromJust <$> HT.lookup src k1
            v2 <- fromJust <$> HT.lookup src k2
            return $ p * v1 * v2
        ) terms
      ShiftLEq terms -> sum <$> mapM (\(p, k) -> (p *) . fromJust <$> (HT.lookup src k)) terms
    HT.insert dst key newV
    return $ checkRes prevCheck newV oldV

approxFixpFrom :: (MonadIO m, Ord n, Fractional n, Show n)
               => LEqSys n -> n -> Int -> ProbVec n -> m ()
approxFixpFrom leqMap eps maxIters probVec
  | maxIters <= 0 = return ()
  | otherwise = do
      -- should be newV >= oldV
      let checkIter leqEps newV oldV =
            -- leqEps && newV - oldV <= eps -- absolute error
            leqEps && (newV == 0 || (newV - oldV) / newV <= eps) -- relative error
      lessThanEps <- evalEqSys leqMap checkIter probVec probVec
      unless lessThanEps $ approxFixpFrom leqMap eps (maxIters - 1) probVec

numLiveEqSys :: (MonadIO m, Ord n, Fractional n, Show n)
            => EqMap n -> m Int
numLiveEqSys eqMap =
  let isLiveEq (PopEq _) = 0
      isLiveEq _ = 1
  in liftIO $ HT.foldM (\acc (_, eq) -> return (acc + isLiveEq eq)) 0 eqMap


-- determine variables for which zero is a fixpoint
preprocessApproxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
                      => EqMap n -> n -> Int -> m [(VarKey, n)]
preprocessApproxFixp eqMap eps maxIters = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMap eqMap
  -- iterate just n and check if fixpoint remains zero
  approxFixpFrom leqMap eps maxIters probVec
  (zeroVars, nonZeroVars) <- liftIO $ MV.foldM (\(acc1, acc2) (varKey, _) -> do
                                p <- fromJust <$> HT.lookup probVec varKey
                                when (p == 0) $ liftIO $ HT.insert eqMap varKey (PopEq 0)
                                if (p == 0)
                                  then return (varKey:acc1, acc2)
                                  else return (acc1, varKey:acc2)
                                ) ([], []) leqMap

  -- replace with the actual values
  let -- apply an operation over a list of maybes
      isLiveSys = length nonZeroVars > 0
      applyOpTerms op = foldl1 (\acc el -> do x <- acc; y<-el; return (op x y))
      immediateValue (PopEq n) = Just n
      immediateValue _ = Nothing
      go (False, updatedVars) = return (updatedVars ++ map (\v -> (v,0)) zeroVars)
      go (True, updatedVars) = foldM (\(recurse, upVars) varKey -> do
          eq <- fromJust <$> HT.lookup eqMap varKey
          case eq of
            PopEq _ -> return (recurse, upVars)
            ShiftEq terms -> do
              eqValue <- applyOpTerms (+) <$> mapM (\(p, k1) -> do
                toEq <- fromJust <$> HT.lookup eqMap k1
                return $ applyOpTerms (*) [Just (fromRational p), immediateValue toEq]
                ) terms
              if isJust eqValue
                then HT.insert eqMap varKey (PopEq (fromJust eqValue)) >> return (True, (varKey, fromJust eqValue) : upVars)
                else return (recurse, upVars)
            PushEq terms -> do
              eqValue <- applyOpTerms (+) <$> mapM (\(p, k1, k2) -> do
                toEq <- fromJust <$> HT.lookup eqMap k1
                toEq2 <- fromJust <$> HT.lookup eqMap k2
                return $ applyOpTerms (*) [Just (fromRational p), immediateValue toEq, immediateValue toEq2]
                ) terms
              if isJust eqValue
                then HT.insert eqMap varKey (PopEq (fromJust eqValue)) >> return (True, (varKey, fromJust eqValue) : upVars)
                else return (recurse, upVars)
        ) (False, updatedVars) nonZeroVars >>= go
  liftIO $ go (isLiveSys, [])

approxFixp :: (MonadIO m, Ord n, Fractional n, Show n)
           => EqMap n -> n -> Int -> m (ProbVec n)
approxFixp eqMap eps maxIters = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMap eqMap
  approxFixpFrom leqMap eps maxIters probVec
  return probVec

defaultEps :: EqMapNumbersType
defaultEps = 1e-8

defaultREps :: Prob
defaultREps = 1 % 10^(8 :: Integer)

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (MonadIO m, RealFrac n) => n -> ProbVec n -> m [(VarKey, Prob, n)]
toRationalProbVec eps probVec =
  liftIO $ map (\(k, p) -> (k, approxRational (p - eps) eps, p)) <$> HT.toList probVec
-- p - eps is to prevent approxRational from producing a result > p

toUpperRationalProbVec :: (MonadIO m, RealFrac n) => n -> ProbVec n -> m [(VarKey, Prob)]
toUpperRationalProbVec eps probVec =
  liftIO $ map (\(k, p) -> (k, approxRational (p + eps) eps)) <$> HT.toList probVec
-- p + eps is to prevent approxRational from producing a result < p
