module Util.System(tempfile,environment,getCC,
                   getLibFlags,getIdrisLibDir,getIncFlags,rmFile) where

-- System helper functions.

import System.Directory (getTemporaryDirectory, removeFile)
import System.FilePath ((</>), addTrailingPathSeparator, normalise)
import System.Environment
import System.IO
import Control.Exception as CE

import Paths_idris

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

getCC :: IO String
getCC = do env <- environment "IDRIS_CC"
           case env of
                Nothing -> return "gcc"
                Just cc -> return cc

tempfile :: IO (FilePath, Handle)
tempfile = do dir <- getTemporaryDirectory
              openTempFile (normalise dir) "idris"

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)

rmFile :: FilePath -> IO ()
rmFile f = do putStrLn $ "Removing " ++ f
              catchIO (removeFile f)
                      (\ioerr -> putStrLn $ "WARNING: Cannot remove file " 
                                 ++ f ++ ", Error msg:" ++ show ioerr)

	
getLibFlags = do dir <- getDataDir
                 return $ "-L" ++ (dir </> "rts") ++ " -lidris_rts -lgmp -lpthread"
                 
getIdrisLibDir = do dir <- getDataDir
                    return $ addTrailingPathSeparator dir

getIncFlags = do dir <- getDataDir
                 return $ "-I" ++ dir </> "rts"
