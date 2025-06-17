{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
   Module      : Pomc.Z3T
   Copyright   : 2024-2025 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Z3T ( Z3T
                , evalZ3TWith
                , liftSTtoIO
                ) where

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.ST (ST, RealWorld, stToIO)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Reader (ReaderT(..), runReaderT, asks)
import Control.Monad.Logger (MonadLogger)
import qualified Z3.Base as B
import Z3.Monad

newtype Z3T m a = Z3T { _unZ3T :: ReaderT Z3TEnv m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadTrans)

data Z3TEnv = Z3TEnv { tenvSolver  :: B.Solver
                     , tenvContext :: B.Context
                     }

instance MonadIO m => MonadZ3 (Z3T m) where
  getSolver  = Z3T $ asks tenvSolver
  getContext = Z3T $ asks tenvContext

instance MonadLogger m => MonadLogger (Z3T m)

evalZ3TWith :: MonadIO m => Maybe Logic -> Opts -> Z3T m a -> m a
evalZ3TWith mbLogic opts (Z3T s) = do
  env <- liftIO $ newEnvWith B.mkContext mbLogic opts
  runReaderT s env

newEnvWith :: (B.Config -> IO B.Context) -> Maybe Logic -> Opts -> IO Z3TEnv
newEnvWith mkContext mbLogic opts =
  B.withConfig $ \cfg -> do
    setOpts cfg opts
    ctx <- mkContext cfg
    solver <- maybe (B.mkSolver ctx) (B.mkSolverForLogic ctx) mbLogic
    return $ Z3TEnv solver ctx

liftSTtoIO :: MonadIO m => ST RealWorld a -> m a
liftSTtoIO = liftIO . stToIO
