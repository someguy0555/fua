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

{-
  <expr>       := equality;
  <equality>   := comparison ( ( "==" "!=" ) comparison )*;
  <comparison> := logical ( ( "<" "<=" ">" ">=" ) logical )*;
  <logical>    := term ( ( "&&" "||" ) term )*;
  <term>       := factor ( ( "+" "-" ) factor)*;
  <factor>     := unary ( ( "*" "/" "%" ) unary )*;
  <unary>      := ( "!" | "-" ) unary | primary;
  <primary>    := <number> | <identifier> | "(" <expr> ")";
-}

data Operator : Nat -> Type where
  Neg          : Operator 1
  Not          : Operator 1
  Add          : Operator 2
  Sub          : Operator 2
  Mul          : Operator 2
  Div          : Operator 2
  Mod          : Operator 2
  And          : Operator 2
  Or           : Operator 2
  Greater      : Operator 2
  Less         : Operator 2
  GreaterEqual : Operator 2
  LessEqual    : Operator 2
  Equal        : Operator 2
  NotEqual     : Operator 2

data ExprType : Type where
  TypeUnknown : ExprType
  TypeNil     : ExprType
  TypeBool    : ExprType
  TypeInt     : ExprType
  TypeReal    : ExprType
  TypeString  : ExprType
  TypeTable   : (SortedMap String ExprType) -> ExprType -- Mapping strings to types.

data Expr : Type where
  ExprOperand  : ExprType -> a -> Expr
  ExprOperator : ExprType -> Operator n -> Vect n Expr -> Expr

expr0 : Expr
expr0 = ExprOperator TypeUnknown Add [ExprOperand TypeUnknown 2, ExprOperand TypeUnknown 2]

parseToken : ( Token -> Bool ) -> Parser (List Token) Token
parseToken predicate =
  do
    tokens <- lift get
    case tokens of
      [] => left "No token found"
      (x::xs) => if predicate x
        then do
          lift . put $ xs
          pure x
        else left $ "token '" ++ "NO_SHOW_IMPLEMENTATION" ++ "' does fulfill predicate"

parseOperator : Operator n -> (Token -> Bool) -> Parser (List Token) ( Operator n )
parseOperator op predicate =
  do
    tokens <- lift get
    case tokens of
      [] => left "No token found"
      (x::xs) => if predicate x
        then do
          lift . put $ xs
          pure op
        else left $ "token '" ++ "NO_SHOW_IMPLEMENTATION" ++ "' does fulfill predicate"

parsePrimary : Parser (List Token) Expr
parsePrimary =
      parseNumber
  <|> parseIdentifier
  <|> parseParens
  where
    parseNumber =
      do
        tok <- parseToken isNumber
        pure $ case tok of
          INTEGER n => ExprOperand TypeInt n
          NUMBER r  => ExprOperand TypeReal r
          _         => ExprOperand TypeUnknown tok

    parseIdentifier =
      do
        tok <- parseToken isIdentifier
        pure $ case tok of
          IDENTIFIER s => ExprOperand TypeUnknown s
          _            => ExprOperand TypeUnknown tok

    parseParens =
      do
        _ <- parseToken (isTokenType LEFT_PAREN)
        e <- parseExpr
        _ <- parseToken (isTokenType RIGHT_PAREN)
        pure e

parseUnary : Parser (List Token) Expr
parseUnary = parseBasic parser
  where
    opParser =
          parseOperator (Not) (isTokenType BANG)
      <|> parseOperator (Neg) (isTokenType MINUS)
    parser = (\pre, post => ExprOperator TypeUnknown pre [post])
      <$> opParser
      <*> parsePrimary

parseFactor : Parser (List Token) Expr
parseFactor = parseBasic parser
  where
    opParser   =
          parseOperator (Mul) (isTokenType STAR)
      <|> parseOperator (Div) (isTokenType SLASH)
      <|> parseOperator (Mod) (isTokenType PERCENT)
    parser = (\pre, inf, post => ExprOperator TypeUnknown inf [pre, post])
      <$> parseUnary
      <*> opParser
      <*> parseUnary

parseTerm : Parser (List Token) Expr
parseTerm = parseBasic parser
  where
    opParser =
          parseOperator Add (isTokenType PLUS)
      <|> parseOperator Sub (isTokenType MINUS)

    parser = (\pre, inf, post =>
                ExprOperator TypeUnknown inf [pre, post])
      <$> parseFactor
      <*> opParser
      <*> parseFactor

parseLogical : Parser (List Token) Expr
parseLogical = parseBasic parser
  where
    opParser =
          parseOperator And (isTokenType AND)
      <|> parseOperator Or  (isTokenType OR)

    parser = (\pre, inf, post =>
                ExprOperator TypeUnknown inf [pre, post])
      <$> parseTerm
      <*> opParser
      <*> parseTerm

parseComparison : Parser (List Token) Expr
parseComparison = parseBasic parser
  where
    opParser =
          parseOperator Greater      (isTokenType GREATER)
      <|> parseOperator GreaterEqual (isTokenType GREATER_EQUAL)
      <|> parseOperator Less         (isTokenType LESS)
      <|> parseOperator LessEqual    (isTokenType LESS_EQUAL)

    parser = (\pre, inf, post =>
                ExprOperator TypeUnknown inf [pre, post])
      <$> parseLogical
      <*> opParser
      <*> parseLogical

parseEquality : Parser (List Token) Expr
parseEquality = parseBasic parser
  where
    opParser =
          parseOperator Equal    (isTokenType EQUAL_EQUAL)
      <|> parseOperator NotEqual (isTokenType BANG_EQUAL)

    parser = (\pre, inf, post =>
                ExprOperator TypeUnknown inf [pre, post])
      <$> parseComparison
      <*> opParser
      <*> parseComparison

parseExpr : Parser (List Token) Expr
parseExpr = parseEquality

