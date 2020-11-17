{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_pomc (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/francescopont/.cabal/bin"
libdir     = "/home/francescopont/.cabal/lib/x86_64-linux-ghc-8.4.4/pomc-0.1.0.0-5UcsEKrC3gL4sN4FxYEbw2"
dynlibdir  = "/home/francescopont/.cabal/lib/x86_64-linux-ghc-8.4.4"
datadir    = "/home/francescopont/.cabal/share/x86_64-linux-ghc-8.4.4/pomc-0.1.0.0"
libexecdir = "/home/francescopont/.cabal/libexec/x86_64-linux-ghc-8.4.4/pomc-0.1.0.0"
sysconfdir = "/home/francescopont/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "pomc_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "pomc_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "pomc_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "pomc_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "pomc_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "pomc_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
