module Pkg.Package where

import System.Process
import System.Directory
import System.Exit
import System.IO

import Util.System

import Control.Monad
import Data.List

import Core.TT
import Idris.REPL
import Idris.AbsSyntax

import Pkg.PParser

import Paths_idris

-- To build a package:
-- * read the package description
-- * check all the library dependencies exist
-- * invoke the makefile if there is one
-- * invoke idris on each module, with idris_opts
-- * install everything into datadir/pname, if install flag is set

buildPkg :: Bool -> (Bool, FilePath) -> IO ()
buildPkg warnonly (install, fp) 
     = do pkgdesc <- parseDesc fp
          ok <- mapM (testLib warnonly (pkgname pkgdesc)) (libdeps pkgdesc)
          when (and ok) $
            do make (makefile pkgdesc)
               dir <- getCurrentDirectory
               setCurrentDirectory $ dir ++ "/" ++ sourcedir pkgdesc
               case (execout pkgdesc) of
                   Nothing -> buildMods (NoREPL : Verbose : idris_opts pkgdesc)
                                    (modules pkgdesc)
                   Just o -> do let exec = dir ++ "/" ++ o
                                buildMod 
                                    (NoREPL : Verbose : Output exec : idris_opts pkgdesc) 
                                    (idris_main pkgdesc)
               setCurrentDirectory dir
               when install $ installPkg pkgdesc

cleanPkg :: FilePath -> IO ()
cleanPkg fp 
     = do pkgdesc <- parseDesc fp
          clean (makefile pkgdesc)
          dir <- getCurrentDirectory
          setCurrentDirectory $ dir ++ "/" ++ sourcedir pkgdesc
          mapM_ rmIBC (modules pkgdesc)
          case execout pkgdesc of
               Nothing -> return ()
               Just s -> do let exec = dir ++ "/" ++ s
                            putStrLn $ "Removing " ++ exec
                            system $ "rm -f " ++ exec 
                            return ()

installPkg :: PkgDesc -> IO ()
installPkg pkgdesc
     = do dir <- getCurrentDirectory
          setCurrentDirectory $ dir ++ "/" ++ sourcedir pkgdesc
          case (execout pkgdesc) of
              Nothing -> mapM_ (installIBC (pkgname pkgdesc)) (modules pkgdesc)
              Just o -> return () -- do nothing, keep executable locally, for noe
          mapM_ (installObj (pkgname pkgdesc)) (objs pkgdesc)

buildMod :: [Opt] -> Name -> IO ()
buildMod opts n = do let f = map slash $ show n
                     idris (Filename f : opts) 
                     return ()
    where slash '.' = '/'
          slash x = x

buildMods :: [Opt] -> [Name] -> IO ()
buildMods opts ns = do let f = map ((map slash) . show) ns
                       idris (map Filename f ++ opts) 
                       return ()
    where slash '.' = '/'
          slash x = x

testLib :: Bool -> String -> String -> IO Bool
testLib warn p f 
    = do d <- getDataDir
         gcc <- getCC
         (tmpf, tmph) <- tempfile
         hClose tmph
         e <- system $ gcc ++ " " ++ d ++ "/rts/libtest.c -l" ++ f ++ " -o " ++ tmpf
         case e of
            ExitSuccess -> return True
            _ -> do if warn 
                       then do putStrLn $ "Not building " ++ p ++ 
                                          " due to missing library " ++ f
                               return False
                       else fail $ "Missing library " ++ f

rmIBC :: Name -> IO ()
rmIBC m = do let f = toIBCFile m 
             putStrLn $ "Removing " ++ f
             system $ "rm -f " ++ f
             return ()
             
toIBCFile (UN n) = n ++ ".ibc"
toIBCFile (NS n ns) = concat (intersperse "/" (reverse ns)) ++ "/" ++ toIBCFile n 

installIBC :: String -> Name -> IO ()
installIBC p m = do let f = toIBCFile m
                    d <- getDataDir
                    let destdir = d ++ "/" ++ p ++ "/" ++ getDest m
                    putStrLn $ "Installing " ++ f ++ " to " ++ destdir
                    system $ "mkdir -p " ++ destdir 
                    system $ "install " ++ f ++ " " ++ destdir
                    return ()
    where getDest (UN n) = ""
          getDest (NS n ns) = concat (intersperse "/" (reverse ns)) ++ "/" ++ getDest n 

installObj :: String -> String -> IO ()
installObj p o = do d <- getDataDir
                    let destdir = d ++ "/" ++ p ++ "/"
                    putStrLn $ "Installing " ++ o ++ " to " ++ destdir
                    system $ "mkdir -p " ++ destdir 
                    system $ "install " ++ o ++ " " ++ destdir
                    return ()

make :: Maybe String -> IO ()
make Nothing = return ()
make (Just s) = do system $ "make -f " ++ s
                   return ()

clean :: Maybe String -> IO ()
clean Nothing = return ()
clean (Just s) = do system $ "make -f " ++ s ++ " clean"
                    return ()



