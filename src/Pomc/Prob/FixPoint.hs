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
                          , LiveEq(..)
                          , LEqSys
                          , ProbVec
                          , mapEqMapPop
                          , addFixpEq
                          , toLiveEqMapWithHints
                          , newVecSameSize
                          , mapVec
                          , copyVec
                          , zeroVec
                          , evalEqSys
                          , approxFixpFrom
                          , approxFixpWithHints
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVecWithHints
                          , preprocessApproxFixpWithHints
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)

import Data.Maybe (fromJust, isJust)
import Data.Ratio (approxRational)
import Control.Monad ( unless, when, foldM, forM )
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (stToIO)
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BHT

import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV

type VarKey = (Int, Int)

data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

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

toLiveEqMapWithHints :: (MonadIO m, Fractional n) => EqMap n -> [VarKey] -> m (LEqSys n)
toLiveEqMapWithHints eqMap lVars = liftIO $ do
  leqMap <- MV.unsafeNew (length lVars)
  n <- liftIO $ foldM
    (\i k -> do
        eq <- fromJust <$> HT.lookup eqMap k
        case eq of
          PushEq terms -> MV.unsafeWrite leqMap i
                          (k, PushLEq $ map (\(p, k1, k2) -> (fromRational p, k1, k2)) terms)
                          >> return (i + 1)
          ShiftEq terms -> MV.unsafeWrite leqMap i
                           (k, ShiftLEq $ map (\(p, k1) -> (fromRational p, k1)) terms)
                           >> return (i + 1)
          _ -> return i
    ) 0 lVars
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

-- determine variables for which zero is a fixpoint
preprocessApproxFixpWithHints :: (MonadIO m, Ord n, Fractional n, Show n)
                      => EqMap n -> n -> Int -> [VarKey] -> m ([(VarKey, n)], [VarKey])
preprocessApproxFixpWithHints eqMap eps maxIters lVars = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMapWithHints eqMap lVars
  -- iterate just n and check if fixpoint remains zero
  approxFixpFrom leqMap eps maxIters probVec
  (zeroVars, nonZeroVars) <- liftIO $ MV.foldM (\(acc1, acc2) (varKey, _) -> do
                                p <- fromJust <$> HT.lookup probVec varKey
                                when (p == 0) $ liftIO $ HT.insert eqMap varKey (PopEq 0)
                                if p == 0
                                  then return (varKey:acc1, acc2)
                                  else return (acc1, varKey:acc2)
                                ) ([], []) leqMap

  let isLiveSys = not (null nonZeroVars)
      applyOpTerms op = foldl1 (\acc el -> do x <- acc; y <- el; return (op x y))
      immediateValue (PopEq n) = Just n
      immediateValue _ = Nothing
      go (False, updatedVars, liveVars)  = return (updatedVars ++ map (\v -> (v,0)) zeroVars, liveVars)
      go (True, updatedVars,liveVars) = foldM (\(recurse, upVars, lVars) varKey -> do
          eq <- fromJust <$> HT.lookup eqMap varKey
          case eq of
            PopEq _ -> error "this is not a live variable"
            ShiftEq terms -> do
              eqValue <- applyOpTerms (+) <$> mapM (\(p, k1) -> do
                toEq <- fromJust <$> HT.lookup eqMap k1
                return $ applyOpTerms (*) [Just (fromRational p), immediateValue toEq]
                ) terms
              if isJust eqValue
                then HT.insert eqMap varKey (PopEq (fromJust eqValue)) >> return (True, (varKey, fromJust eqValue) : upVars, lVars)
                else return (recurse, upVars, varKey: lVars)
            PushEq terms -> do
              eqValue <- applyOpTerms (+) <$> mapM (\(p, k1, k2) -> do
                toEq <- fromJust <$> HT.lookup eqMap k1
                toEq2 <- fromJust <$> HT.lookup eqMap k2
                return $ applyOpTerms (*) [Just (fromRational p), immediateValue toEq, immediateValue toEq2]
                ) terms
              if isJust eqValue
                then HT.insert eqMap varKey (PopEq (fromJust eqValue)) >> return (True, (varKey, fromJust eqValue) : upVars, lVars)
                else return (recurse, upVars, varKey: lVars)
        ) (False, updatedVars, []) liveVars >>= go
  liftIO $ go (isLiveSys, [], nonZeroVars)

approxFixpWithHints :: (MonadIO m, Ord n, Fractional n, Show n)
           => EqMap n -> n -> Int -> [VarKey] -> m (ProbVec n)
approxFixpWithHints eqMap eps maxIters lVars = do
  probVec <- zeroVec eqMap
  leqMap <- toLiveEqMapWithHints eqMap lVars
  approxFixpFrom leqMap eps maxIters probVec
  return probVec

defaultEps :: EqMapNumbersType
defaultEps = 0x1p-26 -- ~ 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVecWithHints :: (MonadIO m, RealFrac n) => n -> ProbVec n -> [VarKey] -> m [(VarKey, Prob)]
toRationalProbVecWithHints eps probVec lVars =
  liftIO $ forM lVars $ \lVar -> (\p -> (lVar, approxRational (p - eps) eps)) . fromJust <$> HT.lookup probVec lVar
-- p - eps is to prevent approxRational from producing a result > p
