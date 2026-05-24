module Main

import Data.List
import Data.SortedMap
import Data.Vect
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

------------------------------------------------------------
-- STATEMENTS
------------------------------------------------------------

data Stmt : Type where
  StmtAssign : Identifier -> Expr -> Stmt
  StmtLabel  : Identifier -> Stmt
  StmtIf     : Expr -> Identifier -> Stmt
  StmtGoto   : Identifier -> Stmt
  StmtPrint  : Expr -> Stmt

covering
Show Stmt where
  show (StmtAssign name expr) =
    name ++ " = " ++ show expr

  show (StmtLabel name) =
    name ++ ":"

  show (StmtIf expr label) =
    "if " ++ show expr ++ " goto " ++ label

  show (StmtGoto label) =
    "goto " ++ label

  show (StmtPrint expr) =
    "print " ++ show expr

------------------------------------------------------------
-- NEWLINES
------------------------------------------------------------

skipNewlines : Parser (List Token) ()
skipNewlines =
  do
    _ <- many (parseToken (isTokenType NEWLINE))
    pure ()

------------------------------------------------------------
-- LABEL
------------------------------------------------------------

parseLabel : Parser (List Token) Stmt
parseLabel =
  do
    toks <- lift get

    case toks of
      (MkToken (IDENTIFIER name) _ _) ::
      (MkToken COLON _ _) :: rest =>
        do
          lift $ put rest
          pure (StmtLabel name)

      _ =>
        left ["Not a label"]

------------------------------------------------------------
-- ASSIGNMENT
------------------------------------------------------------

parseAssign : Parser (List Token) Stmt
parseAssign =
  do
    toks <- lift get

    case toks of
      (MkToken (IDENTIFIER name) _ _) ::
      (MkToken EQUAL _ _) :: rest =>
        do
          lift $ put rest
          expr <- parseExpr
          pure (StmtAssign name expr)

      _ =>
        left ["Not an assignment"]

------------------------------------------------------------
-- IF GOTO
------------------------------------------------------------

parseIfGoto : Parser (List Token) Stmt
parseIfGoto =
  do
    _ <- parseToken (isTokenType IF)

    cond <- parseExpr

    _ <- parseToken (isTokenType GOTO)

    MkToken tok _ _ <- parseToken isIdentifier

    label <- case tok of
               IDENTIFIER s => pure s
               _ => left ["Expected label after goto"]

    pure (StmtIf cond label)

------------------------------------------------------------
-- GOTO
------------------------------------------------------------

parseGoto : Parser (List Token) Stmt
parseGoto =
  do
    _ <- parseToken (isTokenType GOTO)

    MkToken tok _ _ <- parseToken isIdentifier

    label <- case tok of
               IDENTIFIER s => pure s
               _ => left ["Expected label after goto"]

    pure (StmtGoto label)

------------------------------------------------------------
-- PRINT
------------------------------------------------------------

parsePrint : Parser (List Token) Stmt
parsePrint =
  do
    _ <- parseToken (isTokenType PRINT)

    expr <- parseExpr

    pure (StmtPrint expr)

------------------------------------------------------------
-- SINGLE STATEMENT
------------------------------------------------------------

parseStmt : Parser (List Token) Stmt
parseStmt =
      parseIfGoto
  <|> parseGoto
  <|> parsePrint
  <|> parseLabel
  <|> parseAssign

------------------------------------------------------------
-- PROGRAM
------------------------------------------------------------

parseStmtLine : Parser (List Token) Stmt
parseStmtLine =
  do
    stmt <- parseStmt
    skipNewlines
    pure stmt

parseStmtList : Parser (List Token) (List Stmt)
parseStmtList =
  do
    skipNewlines
    many parseStmtLine
