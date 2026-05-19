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

failing
  Show Stmt where
    show (StmtBlock stmts) =
      "{\n" ++ concatMap (\x => show x ++ "\n") stmts ++ "}"

    show (StmtExpr expr) =
      -- "Expr(" ++ show expr ++ ")"
      "Expr(" ++ show expr ++ ")"

    show (StmtIf cond body) =
      "If(" ++ show cond ++ ") " ++ show body

    show (StmtWhile cond body) =
      "While(" ++ show cond ++ ") " ++ show body

    show (StmtReturn Nothing) =
      "Return"

    show (StmtReturn (Just expr)) =
      "Return(" ++ show expr ++ ")"

    show StmtBreak =
      "Break"

    show (StmtAssign name expr) =
      "Assign(" ++ name ++ " = " ++ show expr ++ ")"

    show (StmtLet (name, ty) Nothing) =
      "Let(" ++ name ++ " : " ++ show ty ++ ")"

    show (StmtLet (name, ty) (Just expr)) =
      "Let(" ++ name ++ " : " ++ show ty ++ " = " ++ show expr ++ ")"

    show (StmtFunc (name, retTy) params body) =
      "Fn("
        ++ name
        ++ " : "
        ++ show retTy
        ++ ", params = "
        ++ show params
        ++ ") "
        ++ show body

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

mkFuncType : List ExprType -> ExprType -> ExprType
mkFuncType args ret = TypeFunc args ret

parseFuncStmt =
  do
    _ <- parseToken (tokenTypeIs FN)

    nameTok <- parseToken isIdentifier
    name <- extractName nameTok

    _ <- many parseLineEnd
    _ <- parseToken (tokenTypeIs LEFT_PAREN)
    _ <- many parseLineEnd

    params <- parseParams

    _ <- many parseLineEnd
    _ <- parseToken (tokenTypeIs RIGHT_PAREN)

    retType <- parseOptionalReturnType

    _ <- many parseLineEnd

    body <- parseBlock

    let paramTypes = map snd ( trace ( show params ) params )
    let funcType = TypeFunc paramTypes retType

    pure $
      StmtFunc
        (name, funcType)
        params
        body

  where
    extractName : Token -> Parser (List Token) Identifier
    extractName tok =
      case tok of
        MkToken (IDENTIFIER n) _ _ => pure n
        _ => left ["Expected function name"]

    parseOptionalType : Parser (List Token) ExprType
    parseOptionalType =
      do
        state <- lift get
        case parse parser state of
          (_, Left _) =>
            pure TypeUnknown

          (state', Right ty) =>
            do
              lift $ put state'
              pure ty
      where
        parser =
          do
            _ <- many parseLineEnd
            _ <- parseToken (tokenTypeIs COLON)
            _ <- many parseLineEnd
            parseExprType

    parseParam : Parser (List Token) IdentifierAndType
    parseParam =
      do
        tok <- parseToken isIdentifier

        name <-
          case tok of
            MkToken (IDENTIFIER n) _ _ => pure n
            _ => left ["Expected parameter name"]

        ty <- parseOptionalType
        pure (name, ty)

    optionalParam : Parser (List Token) (Maybe IdentifierAndType)
    optionalParam =
          (do p <- parseParam; pure (Just p))
      <|> pure Nothing

    parseParams : Parser (List Token) (List IdentifierAndType)
    parseParams =
      do
        first <- optionalParam

        case first of
          Nothing => pure []
          Just x =>
            do
              xs <- many $
                do
                  _ <- many parseLineEnd
                  _ <- parseToken (tokenTypeIs COMMA)
                  _ <- many parseLineEnd
                  parseParam
              pure (x :: xs)

    parseOptionalReturnType : Parser (List Token) ExprType
    parseOptionalReturnType =
      parseOptionalType
-- parseFuncStmt =
--   do
--     _ <- parseToken (tokenTypeIs FN)
--
--     nameTok <- parseToken isIdentifier
--     name <- extractName nameTok
--
--     _ <- many parseLineEnd
--     _ <- parseToken (tokenTypeIs LEFT_PAREN)
--     _ <- many parseLineEnd
--
--     params <- parseParams
--
--     _ <- many parseLineEnd
--     _ <- parseToken (tokenTypeIs RIGHT_PAREN)
--
--     retType <- parseOptionalReturnType
--
--     _ <- many parseLineEnd
--
--     body <- parseBlock
--
--     pure $
--       StmtFunc
--         (name, retType)
--         params
--         body
--
--   where
--     extractName             : Token -> Parser (List Token) Identifier
--     parseOptionalType       : Parser (List Token) ExprType
--     parseParam              : Parser (List Token) IdentifierAndType
--     parseParams             : Parser (List Token) (List IdentifierAndType)
--     optionalParam           : Parser (List Token) (Maybe IdentifierAndType)
--     parseOptionalReturnType : Parser (List Token) ExprType
--
--     extractName tok =
--       case tok of
--         MkToken (IDENTIFIER n) _ _ =>
--           pure n
--
--         _ =>
--           left ["Expected function name"]
--
--     parseOptionalType =
--       do
--         state <- lift get
--
--         case parse parser state of
--           (_, Left _) =>
--             pure TypeUnknown
--
--           (state', Right ty) =>
--             do
--               lift $ put state'
--               pure ty
--
--       where
--         parser : Parser (List Token) ExprType
--         parser =
--           do
--             _ <- many parseLineEnd
--             _ <- parseToken (tokenTypeIs COLON)
--             _ <- many parseLineEnd
--             parseExprType
--
--     parseParam =
--       do
--         tok <- parseToken isIdentifier
--
--         name <-
--           case tok of
--             MkToken (IDENTIFIER n) _ _ =>
--               pure n
--
--             _ =>
--               left ["Expected parameter name"]
--
--         ty <- parseOptionalType
--
--         pure (name, ty)
--
--     parseParams =
--       do
--         first <- optionalParam
--
--         case first of
--           Nothing =>
--             pure []
--
--           Just x =>
--             do
--               xs <- many $
--                 do
--                   _ <- many parseLineEnd
--                   _ <- parseToken (tokenTypeIs COMMA)
--                   _ <- many parseLineEnd
--                   parseParam
--
--               pure (x :: xs)
--
--     optionalParam =
--           (do p <- parseParam; pure (Just p))
--       <|> pure Nothing
--
--     parseOptionalReturnType =
--       parseOptionalType

parseProgram : Parser (List Token) Stmt
parseProgram =
  do
    _ <- many parseLineEnd

    stmts <- parseStmts

    _ <- many parseLineEnd

    remaining <- lift get

    case remaining of
      [] =>
        pure (StmtBlock stmts)

      [MkToken EOF _ _] =>
        pure (StmtBlock stmts)

      toks =>
        left ["Unexpected tokens at end of program: " ++ show toks]
