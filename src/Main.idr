module Main

import Data.List
import Data.SortedMap
import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Debug.Trace
import System.File

import Parser
import Lexer
import Expr
import Utility

parseCode : String -> Either ErrorMsg Expr
parseCode src =
  case parseText lexer src of
    (_, Left lexErr) => Left lexErr
    (_, Right toks) =>
      case parse (parseExpr) toks of
        (tokan, Left lf) => Left lf
        (tokan, Right e) => Right e

expr00 = "2 + 3 * 3"
