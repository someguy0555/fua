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

-- data Expr : Type where
--   ExprOperand  : ExprType -> a -> Expr
--   ExprOperator : ExprType -> Operator n -> Vect n Expr -> Expr

data Stmt : Type where
  StmtIf     : Expr -> (List Stmt) -> Stmt
  StmtWhile  : Expr -> (List Stmt) -> Stmt
  StmtLet    : String -> Expr -> Stmt
  StmtAssign : String -> Expr -> Stmt
  StmtBreak  : Stmt

tokenTypeIs : TokenType -> Token -> Bool
tokenTypeIs tt (MkToken tok _ _) = tt == tok

isLineEnd : TokenType -> Bool
isLineEnd tt = tt == NEWLINE || tt == SEMICOLON

parseLineEnd : Parser (List Token) ()
parseLineEnd =
  do
    _ <- (
      parseToken (tokenTypeIs NEWLINE)
      <|>
      parseToken (tokenTypeIs SEMICOLON)
      )
    pure ()

parseStmt  : Parser (List Token) Stmt
parseStmts : Parser (List Token) (List Stmt)
parseIfStmt : Parser (List Token) Stmt
parseWhileStmt : Parser (List Token) Stmt
parseBreakStmt : Parser (List Token) Stmt
parseAssignStmt : Parser (List Token) Stmt

parseStmt =
      parseIfStmt
  <|> parseWhileStmt
  <|> parseBreakStmt
  <|> parseAssignStmt

parseStmts =
  do
    uhh <- many (
      do
        stmt <- parseStmt
        _    <- parseLineEnd
        pure stmt
      )
    pure uhh

parseIfStmt =
  do
    _ <- parseToken (tokenTypeIs IF)
    _ <- many parseLineEnd
    condition <- ?parseCondition_if
    _ <- many parseLineEnd
    _ <- parseToken (tokenTypeIs LEFT_BRACE)
    _ <- many parseLineEnd
    nested <- parseStmts
    _ <- parseToken (tokenTypeIs RIGHT_BRACE)
    pure $ StmtIf condition nested

parseWhileStmt =
  do
    _ <- parseToken (tokenTypeIs IF)
    _ <- many parseLineEnd
    condition <- parseExpr
    _ <- parseToken (tokenTypeIs LEFT_BRACE)
    _ <- many parseLineEnd
    nested <- parseStmts
    _ <- parseToken (tokenTypeIs RIGHT_BRACE)
    pure $ StmtWhile condition nested

parseBreakStmt =
  do
    _ <- parseToken (tokenTypeIs BREAK)
    pure $ StmtBreak

parseAssignStmt =
  do
    tok <- parseToken isIdentifier
    case tok of
      MkToken (IDENTIFIER name) _ _ => do
        _ <- many parseLineEnd
        _ <- parseToken (tokenTypeIs EQUAL)
        _ <- many parseLineEnd
        value <- parseExpr
        pure (StmtAssign name value)
      _ => left ["Failed to parse identifier"]

{-
  parseBasic
-}
