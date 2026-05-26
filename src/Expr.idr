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
import Utility

Identifier = String

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

data Expr : Type where
  ExprOperand    : Integer -> Expr
  ExprVariable   : Identifier -> Expr
  ExprOperator   : Operator n -> Vect n Expr -> Expr

Show (Operator n) where
  show Neg          = "Neg"
  show Not          = "Not"
  show Add          = "Add"
  show Sub          = "Sub"
  show Mul          = "Mul"
  show Div          = "Div"
  show Mod          = "Mod"
  show And          = "And"
  show Or           = "Or"
  show Greater      = "Greater"
  show Less         = "Less"
  show GreaterEqual = "GreaterEqual"
  show LessEqual    = "LessEqual"
  show Equal        = "Equal"
  show NotEqual     = "NotEqual"

-- Your mother is not total.
covering
Show Expr where
  show (ExprOperand val) =
    "Operand(" ++ show val ++ ")"

  show (ExprVariable name) =
    "Variable(" ++ name ++ ")"

  show (ExprOperator op exprs) =
    "Operator("
      ++ show op
      ++ ", "
      ++ show exprs
      ++ ")"

expr0 : Expr
expr0 = ExprOperator Add [ExprOperand 2, ExprOperand 2]

myTrace : (msg : String) -> (result : a) -> a
myTrace x val = force $ unsafePerformIO (do putStrLn x; pure val)

parseOperator : Operator n -> (Token -> Bool) -> Parser (List Token) (Operator n)
parseOperator op predicate =
  do
    t <- parseToken (\x => predicate x)
    pure op
-- parseOperator : Operator n -> (Token -> Bool) -> Parser (List Token) ( Operator n )
-- parseOperator op predicate =
--   do
--     tokens <- lift get
--     case tokens of
--       [] => left [ "No token found" ]
--       (x::xs) => if predicate x
--         then do
--           lift . put $ xs
--           pure op
--         else left [ "parseOperator: token '" ++ (show x) ++ "' in '" ++ show tokens ++ "' does not fulfill predicate" ]

parseOperatorUsingTokenType : Operator n -> TokenType -> Parser (List Token) (Operator n)
parseOperatorUsingTokenType op tt =
  do
    _ <- parseToken (isTokenType tt)
    pure op

parseLeftAssoc : Parser (List Token) Expr ->
                  Parser (List Token) (Operator 2) ->
                  Parser (List Token) Expr
parseLeftAssoc lowerParser opParser =
  do
    first <- lowerParser
    loop first
  where
    loop leftExpr =
      (do
          op <- opParser
          rhs <- lowerParser
          loop (ExprOperator op [leftExpr, rhs])
      )
      <|> pure leftExpr

parsePrimary         : Parser (List Token) Expr
parseUnary           : Parser (List Token) Expr
parseExpr            : Parser (List Token) Expr
parseFactor          : Parser (List Token) Expr
parseTerm            : Parser (List Token) Expr
parseLogical         : Parser (List Token) Expr
parseComparison      : Parser (List Token) Expr
parseEquality        : Parser (List Token) Expr

parsePrimary =
      parseNumber
  <|> parseIdentifier
  <|> parseParens
  where
    parseNumber =
      do
        MkToken tok _ _ <- parseToken isIntegerToken
        case tok of
          INTEGER n => pure $ ExprOperand n
          _         => left ["Unable to parse number"]

    parseIdentifier =
      do
        MkToken tok _ _ <- parseToken isIdentifier
        case tok of
          IDENTIFIER s => pure $ ExprVariable s
          _            => left ["Unable to parse identifier"]

    parseParens =
      do
        _ <- parseToken (isTokenType LEFT_PAREN)
        e <- parseExpr
        _ <- parseToken (isTokenType RIGHT_PAREN)
        pure e

parseUnary =
      parseUnaryOp
  <|> parsePrimary
  where
    opParser : Parser (List Token) (Operator 1)
    opParser =
          parseOperatorUsingTokenType Not BANG
      <|> parseOperatorUsingTokenType Neg MINUS

    parseUnaryOp : Parser (List Token) Expr
    parseUnaryOp =
      do
        op <- opParser
        e  <- parseUnary
        pure $ ExprOperator op [e]

-- Left-associative
parseFactor =
  parseLeftAssoc parseUnary opParser
  where
    opParser =
          parseOperatorUsingTokenType Mul STAR
      <|> parseOperatorUsingTokenType Div SLASH
      <|> parseOperatorUsingTokenType Mod PERCENT

-- Left-associative
parseTerm =
  parseLeftAssoc parseFactor opParser
  where
    opParser =
          parseOperatorUsingTokenType Add PLUS
      <|> parseOperatorUsingTokenType Sub MINUS

-- Left-associative
parseLogical =
  parseLeftAssoc parseTerm opParser
  where
    opParser =
          parseOperatorUsingTokenType And AMPERSAND
      <|> parseOperatorUsingTokenType Or  PIPE

-- Left-associative
parseComparison =
  parseLeftAssoc parseLogical opParser
  where
    opParser =
          parseOperatorUsingTokenType Greater GREATER
      <|> parseOperatorUsingTokenType GreaterEqual GREATER_EQUAL
      <|> parseOperatorUsingTokenType Less LESS
      <|> parseOperatorUsingTokenType LessEqual LESS_EQUAL

-- Left-associative
parseEquality =
  parseLeftAssoc parseComparison opParser
  where
    opParser =
          parseOperatorUsingTokenType Equal EQUAL_EQUAL
      <|> parseOperatorUsingTokenType NotEqual BANG_EQUAL

parseExpr =
  parseEquality
  -- (parserOverwriteError (\err => err ++ ["parseEquality in parseExpr failed"]) $ parseEquality )

------------------------------------------------------------
-- TYPED STATE MACHINE
------------------------------------------------------------

record ExprEnv where
  constructor MkExprEnv
  symbols : SortedMap Identifier Integer

data EvalStep : Type where
  StepEval : ExprEnv -> Expr -> EvalStep

data Frame
  = EvalR Expr
  | EvalOp2L (Integer -> Integer -> Integer) Expr
  | EvalOp2R (Integer -> Integer -> Integer) Integer

data EvalState
  = Running ExprEnv Expr (List Frame)
  | Done ExprEnv Integer

unwind : ExprEnv -> Integer -> List Frame -> EvalState
step : EvalState -> EvalState
evalExpr : ExprEnv -> Expr -> Integer
runExpr : ExprEnv -> Expr -> Integer

step (Done env v) = Done env v

-- Evaluate a literal
step (Running env (ExprOperand n) stack) =
  case stack of
    [] => Done env n
    _  => unwind env n stack

-- Evaluate variable
step (Running env (ExprVariable x) stack) =
  let v =
        case SortedMap.lookup x env.symbols of
          Just v' => v'
          Nothing  => 0
  in
    case stack of
      [] => Done env v
      _  => unwind env v stack


-- Operator application (dispatch)
step (Running env (ExprOperator op args) stack) =
  case op of

    Add =>
      case args of
        [a,b] => Running env a ((EvalOp2L (+) b) :: stack)
        _     => Done env 0

    Sub =>
      case args of
        [a,b] => Running env a (EvalOp2L (-) b :: stack)
        _     => Done env 0

    Mul =>
      case args of
        [a,b] => Running env a (EvalOp2L (*) b :: stack)
        _     => Done env 0

    Div =>
      case args of
        [a,b] => Running env a (EvalOp2L div b :: stack)
        _     => Done env 0

    Mod =>
      case args of
        [a,b] => Running env a (EvalOp2L mod b :: stack)
        _     => Done env 0

    Neg =>
      case args of
        [a] => Running env a (EvalOp2L (\x, y => 0 - x) (ExprOperand 0) :: stack)
        _   => Done env 0

    Not =>
      case args of
        [a] => Running env a (EvalOp2L (\x, _ => if x == 0 then 1 else 0) (ExprOperand 0) :: stack)
        _   => Done env 0

    Equal =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x == y then 1 else 0) b :: stack)
        _     => Done env 0

    NotEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= y then 1 else 0) b :: stack)
        _     => Done env 0

    Less =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x < y then 1 else 0) b :: stack)
        _     => Done env 0

    Greater =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x > y then 1 else 0) b :: stack)
        _     => Done env 0

    LessEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x <= y then 1 else 0) b :: stack)
        _     => Done env 0

    GreaterEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x >= y then 1 else 0) b :: stack)
        _     => Done env 0

    And =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= 0 && y /= 0 then 1 else 0) b :: stack)
        _     => Done env 0

    Or =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= 0 || y /= 0 then 1 else 0) b :: stack)
        _     => Done env 0

unwind env v [] = Done env v

unwind env v (EvalOp2L f rhs :: stack) =
  Running env rhs (EvalOp2R f v :: stack)

unwind env v (EvalOp2R f v1 :: stack) =
  let v' = f v1 v
  in unwind env v' stack

unwind env v (EvalR e :: stack) =
  Running env e (EvalOp2R (\x, y => x) v :: stack)

evalExpr env e =
  case step (Running env e []) of
    Done _ v => v
    Running env' e' st => evalExpr env' e'

runExpr env e = go (Running env e [])
  where
    go : EvalState -> Integer
    go (Done _ v) = v
    go st =
      go (step st)
