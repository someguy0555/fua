module Main

import Data.List
import Data.SortedMap
import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Debug.Trace
import System
import System.File

import Parser
import Lexer
import Expr
import Stmt
import Resolve
import Interpreter
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

parseProgram : String -> Either ErrorMsg (List Stmt)
parseProgram src =
  case parseText lexer src of
    (_, Left lexErr) =>
      Left lexErr

    (_, Right toks) =>
      case parse parseStmtList toks of
        (remaining, Left parseErr) =>
          Left parseErr

        ([], Right stmts) =>
          Right stmts

        (remaining, Right stmts) =>
          Left
            [ "Unconsumed tokens: " ++ show remaining ]

runProgram : List Stmt -> IO ()
runProgram stmts =
  case checkProgram stmts of
    Left err => printLn err
    Right env =>
      do
        -- printLn $ "stmts: " ++ show stmts
        -- printLn env
        -- printLn "Program check successful"
        final <- exec stmts env 0
        pure ()

execProgram : String -> IO ()
execProgram src = do
  case parseText lexer src of
    (_, Left err) => printLn err

    (_, Right tokens) =>
      case parse parseStmtList tokens of
        (_, Left perr) => printLn perr

        (_, Right stmts) => do
          -- printLn $ "Why does this not work? "
          -- printLn $ show src
          _ <- runProgram stmts
          pure ()

execFile : String -> IO ()
execFile path =
  do
    res <- readFile path
    case res of
      Left err =>
        do
          printLn ("File error: " ++ show err)
      Right content =>
        do
          _ <- execProgram content
          pure ()

main : IO ()
main =
  do
    args <- getArgs

    case args of
      (_ :: path :: _) =>
        execFile path

      _ =>
        printLn "Usage: program <file>"

code00 = """
a = 0
b = 1
repeat:
if b > 100 goto fib
c = a + b
a = b
b = c
print c
if 1 goto repeat
fib:
"""

