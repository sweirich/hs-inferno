module Paths_hs_inferno (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/sweirich/Library/Haskell/ghc-7.8.3/lib/hs-inferno-0.1.0.0/bin"
libdir     = "/Users/sweirich/Library/Haskell/ghc-7.8.3/lib/hs-inferno-0.1.0.0/lib"
datadir    = "/Users/sweirich/Library/Haskell/ghc-7.8.3/lib/hs-inferno-0.1.0.0/share"
libexecdir = "/Users/sweirich/Library/Haskell/ghc-7.8.3/lib/hs-inferno-0.1.0.0/libexec"
sysconfdir = "/Users/sweirich/Library/Haskell/ghc-7.8.3/lib/hs-inferno-0.1.0.0/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "hs_inferno_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "hs_inferno_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "hs_inferno_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "hs_inferno_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "hs_inferno_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
