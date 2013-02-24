module IRTS.CodegenCommon where

import Core.TT
import IRTS.Simplified

import Control.Exception
import System.Environment

data DbgLevel = NONE | DEBUG | TRACE deriving Eq
data OutputType = Raw | Object | Executable deriving (Eq, Show)
