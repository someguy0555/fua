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

IdentifierAndType : Type
IdentifierAndType  = (Identifier, ExprType)
-- data Expr : Type where
--   ExprOperand  : ExprType -> a -> Expr
--   ExprOperator : ExprType -> Operator n -> Vect n Expr -> Expr

data Stmt : Type where
  StmtBlock  : List Stmt -> Stmt
  StmtExpr   : Expr -> Stmt
  StmtIf     : Expr -> Stmt -> Stmt
  StmtWhile  : Expr -> Stmt -> Stmt
  StmtReturn : Maybe Expr -> Stmt
  StmtBreak  : Stmt
  StmtAssign : Identifier -> Expr -> Stmt
  StmtLet    : IdentifierAndType -> Maybe Expr -> Stmt
  StmtFunc   : IdentifierAndType -> List IdentifierAndType -> Stmt -> Stmt

isLineEnd : TokenType -> Bool
isLineEnd tt = tt == NEWLINE || tt == SEMICOLON

parseStmt       : Parser (List Token) Stmt
parseStmts      : Parser (List Token) (List Stmt)
parseBlock      : Parser (List Token) Stmt
parseExprStmt   : Parser (List Token) Stmt
parseIfStmt     : Parser (List Token) Stmt
parseReturnStmt : Parser (List Token) Stmt
parseWhileStmt  : Parser (List Token) Stmt
parseBreakStmt  : Parser (List Token) Stmt
parseAssignStmt : Parser (List Token) Stmt
parseLetStmt    : Parser (List Token) Stmt
parseFuncStmt   : Parser (List Token) Stmt

parseStmt =
      parseIfStmt
  <|> parseWhileStmt
  <|> parseReturnStmt
  <|> parseBreakStmt
  <|> parseAssignStmt
  <|> parseLetStmt
  <|> parseFuncStmt
  <|> parseExprStmt
  <|> parseBlock

parseStmts =
  do
    uhh <- many (
      do
        stmt <- parseStmt
        _    <- many parseLineEnd
        pure stmt
      )
    pure uhh

parseBlock =
  do
    _ <- parseToken (tokenTypeIs LEFT_BRACE)
    _ <- many parseLineEnd

    stmts <- parseStmts

    _ <- many parseLineEnd
    _ <- parseToken (tokenTypeIs RIGHT_BRACE)

    pure (StmtBlock stmts)

parseExprStmt =
  do
    expr <- parseExpr
    pure $ StmtExpr expr

parseIfStmt =
  do
    _ <- parseToken (tokenTypeIs IF)
    _ <- many parseLineEnd
    condition <- parseExpr
    _ <- many parseLineEnd
    body <- parseBlock
    pure $ StmtIf condition body

parseWhileStmt =
  do
    _ <- parseToken (tokenTypeIs WHILE)
    _ <- many parseLineEnd
    condition <- parseExpr
    _ <- many parseLineEnd
    body <- parseBlock
    pure $ StmtWhile condition body

parseBreakStmt =
  do
    _ <- parseToken (tokenTypeIs BREAK)
    pure $ StmtBreak

parseRightHandSide : Parser (List Token) Expr
parseRightHandSide =
  do
    _ <- parseToken (tokenTypeIs EQUAL)
    _ <- many parseLineEnd
    parseExpr

parseAssignStmt =
  do
    tok <- parseToken isIdentifier
    case tok of
      MkToken (IDENTIFIER name) _ _ => do
        _ <- many parseLineEnd
        value <- parseRightHandSide
        pure (StmtAssign name value)
      _ => left ["Failed to parse identifier"]

parseLetStmt =
  do
    _ <- parseToken (tokenTypeIs LET)
    tok <- parseToken isIdentifier
    case tok of
      MkToken (IDENTIFIER name) _ _ => do
        _ <- many parseLineEnd
        parsedType <- many $ do
          _ <- parseToken (tokenTypeIs COLON)
          _ <- many parseLineEnd
          parseExprType
        realType <-
          case parsedType of
               []      => pure TypeUnknown
               [x]     => pure x
               _       => left ["Attempting to define type multiple times"]
              -- _        => left [ "Attempting to define type of declaration multiple times." ]
        parsedValue <- do
          _ <- many parseLineEnd
          many parseRightHandSide
        realValue <-
          case parsedValue of
               []      => pure (Nothing)
               [x]     => pure (Just x)
               _       => left ["Attempting to assign multiple values"]
        pure (StmtLet (name, realType) realValue)
      _ => left ["Failed to parse identifier"]

parseReturnStmt =
  do
    _ <- parseToken (tokenTypeIs RETURN)

    exprs <- many parseExpr

    case exprs of
         []    => pure (StmtReturn Nothing)
         [x]   => pure (StmtReturn (Just x))
         _     => left ["Invalid return statement"]

parseFuncStmt =
  do
    _ <- parseToken (tokenTypeIs FN)

    nameTok <- parseToken isIdentifier

    (name, retType) <- extractName nameTok

    _ <- parseToken (tokenTypeIs LEFT_PAREN)
    _ <- many parseLineEnd

    params <- parseParams

    _ <- many parseLineEnd
    _ <- parseToken (tokenTypeIs RIGHT_PAREN)

    _ <- many parseLineEnd

    body <- parseBlock

    pure (StmtFunc (name, retType) params body)

  where
    extractName : Token -> Parser (List Token) (String, ExprType)
    extractName tok =
      case tok of
        MkToken (IDENTIFIER n) _ _ =>
          pure (n, TypeUnknown)
        _ =>
          left ["Expected function name"]

    parseParams : Parser (List Token) (List IdentifierAndType)
    parseParams =
      many $
        do
          t <- parseToken isIdentifier
          case t of
            MkToken (IDENTIFIER n) _ _ =>
              pure (n, TypeUnknown)
            _ =>
              left ["Invalid parameter"]

parseProgram : Parser (List Token) (List Stmt)
parseProgram =
  do
    pure []

-- parseLetStmt =
--   do
--     _ <- parseToken (tokenTypeIs LET)
--     tok <- parseToken isIdentifier
--     case tok of
--       MkToken (IDENTIFIER name) _ _ => do
--         _ <- many parseLineEnd
--         parsedType <- many $ do
--           _ <- parseToken (tokenTypeIs COLON)
--           _ <- many parseLineEnd
--           parseExprType
--         let realType =
--           case parsedType of
--               [] => TypeUnknown
--               (x::[])  => x
--               _  => left [ "Attempting to define type of declaration multiple times." ]
--         _ <- many parseLineEnd
--         parsedValue <- do
--           _ <- many parseLineEnd
--           many parseRightHandSide
--         let realValue =
--           case parsedValue of
--               [] => ExprUnassigned TypeUnknown
--               (x::[])  => x
--               _  => left [ "Attempting to assign value to variable multiple times." ]
--         pure (StmtLet (name, realType) realValue)
--         -- pure (StmtLet (?name, ?realType) ?realValue)
--       _ => left ["Failed to parse identifier"]

{-
  parseBasic
-}
