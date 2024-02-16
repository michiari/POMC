{- |
   Module      : Pomc.LogUtils
   Copyright   : 2024 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.LogUtils ( MonadLogger(..)
                     , ToLogStr
                     , LogVerbosity
                     , LogLevel(..)
                     , LoggingT
                     , selectLogVerbosity
                     , logDebugN
                     , logInfoN
                     ) where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger hiding (logDebugN, logInfoN)
import Control.Monad.Trans (lift)
import Data.Text as T
import Z3.Monad (MonadZ3(..))

instance MonadZ3 m => MonadZ3 (LoggingT m) where
  getSolver = lift getSolver
  getContext = lift getContext

type LogVerbosity = Maybe LogLevel

runDisabledLoggingT :: MonadIO m => LoggingT m a -> m a
runDisabledLoggingT = (`runLoggingT` noOutput)
  where noOutput _ _ _ _ = return ()

selectLogVerbosity :: MonadIO m => LogVerbosity -> LoggingT m a -> m a
selectLogVerbosity Nothing = runDisabledLoggingT
selectLogVerbosity (Just level) = runStderrLoggingT . filterLogger (\_ lvl -> lvl >= level)

logDebugN :: (MonadLogger m, ToLogStr msg) => msg -> m ()
logDebugN = logWithoutLoc T.empty LevelDebug

logInfoN :: (MonadLogger m, ToLogStr msg) => msg -> m ()
logInfoN = logWithoutLoc T.empty LevelInfo
