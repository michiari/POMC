{- |
   Module      : Pomc.Prob.EqSolver
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
module Pomc.Prob.EqSolver ( solveEqSystem
                          ) where

import Pomc.SatUtil(freshIONegId)

import Data.Set(Set)
import qualified Data.Set as Set

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import Control.Monad (when, forM_)
import Data.IORef (IORef, newIORef)
import Pomc.Prob.FixPoint (VarKey, EqMap, retrieveEquation, FixpEq (..))
import qualified Data.HashTable.IO as BH
import Data.Maybe (fromJust)
import Pomc.LogUtils (MonadLogger)
import Control.Monad.IO.Class (MonadIO(liftIO))

-- mutable global data structures of this module
data SolverGlobals = SolverGlobals
  { negIdSeq  :: IORef Int
  , sStack    :: IOStack VarKey
  , bStack    :: IOStack Int
  , iVector   :: BH.BasicHashTable VarKey Int
  , eqMap     :: EqMap (Double, Double)
  }

newSolverGlobals :: Set VarKey -> EqMap (Double, Double) -> IO SolverGlobals
newSolverGlobals lVars eqMap_ = do
  newIdSeq <- newIORef (-1)
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVect <- BH.newSized (Set.size lVars)
  return SolverGlobals  { negIdSeq = newIdSeq
                          , sStack = newSStack
                          , bStack = newBStack
                          , iVector = newIVect
                          , eqMap = eqMap_
                        }

-- solve the current set of live variables in a decomposed fashion
-- that is, identify bottom SCCs, solve them, and iterate
solveEqSystem :: (MonadIO m, MonadLogger m)
  => EqMap (Double, Double)
  -> Set VarKey
  -> (EqMap (Double, Double) -> VarKey -> FixpEq (Double, Double) ->  m ())
  -> ([VarKey] -> m ())
  -> m ()
solveEqSystem eqMap_ lVars solveSingle solveSCC = do
  globals <- liftIO $ newSolverGlobals lVars eqMap_
  -- explore the graph
  forM_ (Set.elems lVars)
    (\varKey -> do
      iVal <- liftIO $ lookupIValue globals varKey
      when (iVal == 0) $ do
        liftIO $ addtoPath globals varKey
        dfs globals solveSingle solveSCC lVars varKey
    )

dfs :: (MonadIO m, MonadLogger m)
  => SolverGlobals
  -> (EqMap (Double, Double) -> VarKey -> FixpEq (Double, Double) ->  m ())
  -> ([VarKey] -> m ())
  -> Set VarKey
  -> VarKey
  -> m ()
dfs globals solveSingle solveSCC lVars varKey =
  let collectSuccPush [] = []
      collectSuccPush ((_, varKey1, varKey2):l)
        | memb1 && memb2 = varKey1:varKey2:collectSuccPush l
        | memb1 = varKey1:collectSuccPush l
        | memb2 = varKey2:collectSuccPush l
        | otherwise = collectSuccPush l
        where
          memb1 = Set.member varKey1 lVars
          memb2 = Set.member varKey2 lVars

      collectSuccShift [] = []
      collectSuccShift ((_, varKey1):l)
        | Set.member varKey1 lVars = varKey1:collectSuccShift l
        | otherwise = collectSuccShift l

      succs (PushEq l) = collectSuccPush l
      succs (ShiftEq l) = collectSuccShift l
      succs (PopEq _) = error "cannot follow already dead equation."

      cases nextVarKey nextIVal
        | (nextIVal == 0) = do
            liftIO $ addtoPath globals nextVarKey
            dfs globals solveSingle solveSCC lVars nextVarKey
        | (nextIVal < 0)  = return ()
        | (nextIVal > 0)  = liftIO $ do
          -- push to keep track of self cycles in createComponent
          IOGS.push (sStack globals) nextVarKey
          merge globals nextVarKey

      follow nextVarKey = (liftIO (lookupIValue globals nextVarKey) >>= cases nextVarKey)
  in do
    eq <- liftIO $ fromJust <$> retrieveEquation (eqMap globals) varKey
    mapM_ follow (succs eq)
    createComponent globals solveSingle solveSCC eq varKey

createComponent :: (MonadIO m, MonadLogger m)
  => SolverGlobals
  -> (EqMap (Double, Double) -> VarKey -> FixpEq (Double, Double) ->  m ())
  -> ([VarKey] -> m ())
  -> FixpEq (Double, Double)
  -> VarKey
  -> m ()
createComponent globals solveSingle solveSCC eq varKey = do
  topB <- liftIO $ IOGS.peek $ bStack globals
  iVal <- liftIO $ lookupIValue globals varKey
  let cases
        | iVal /= topB = return ()
        | otherwise = do
          -- updating data structures of Gabow algorithm
          sccId <- liftIO $ freshIONegId (negIdSeq globals)
          liftIO $ IOGS.pop_ (bStack globals)
          sSize <- liftIO $ IOGS.size $ sStack globals
          -- the last one is the current varKey
          poppedVarKeys <- liftIO $ IOGS.multPop (sStack globals) (sSize - iVal + 1)
          liftIO $ forM_ poppedVarKeys $ \k -> BH.insert (iVector globals) k sccId
          -- solve the SCC
          case poppedVarKeys of
            [varKey] -> solveSingle (eqMap globals) varKey eq
            _ -> solveSCC poppedVarKeys
  cases

-- Gabow helpers
lookupIValue :: SolverGlobals -> VarKey -> IO Int
lookupIValue globals varKey = do
  maybeIval <- BH.lookup (iVector globals) varKey
  maybe (return 0) return maybeIval

addtoPath :: SolverGlobals -> VarKey -> IO ()
addtoPath globals varKey = do
  IOGS.push (sStack globals) varKey
  sSize <- IOGS.size $ sStack globals
  BH.insert (iVector globals) varKey sSize
  IOGS.push (bStack globals) sSize

merge ::  SolverGlobals -> VarKey -> IO ()
merge globals varKey = do
  iVal <- lookupIValue globals varKey
  -- contract the B stack, carrying boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)
