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

parseOperator : Operator n -> (Token -> Bool) -> Parser (List Token) ( Operator n )
parseOperator op predicate =
  do
    tokens <- lift get
    case tokens of
      [] => left [ "No token found" ]
      (x::xs) => if predicate x
        then do
          lift . put $ xs
          pure op
        else left [ "parseOperator: token '" ++ (show x) ++ "' in '" ++ show tokens ++ "' does not fulfill predicate" ]

parseOperatorUsingTokenType : Operator n -> TokenType -> Parser (List Token) (Operator n)
parseOperatorUsingTokenType op tt =
  parserOverwriteError
    (modifyLastError (\txt => "Failed to parse operator using token type '" ++ show tt ++ "' in: " ++ txt))
    $
    parseOperator op (isTokenType tt)

parseLeftAssoc : Parser (List Token) Expr -> Parser (List Token) (Operator 2) -> Parser (List Token) Expr
parseLeftAssoc lowerParser opParser =
  do
    first <- lowerParser
    continue first

  where
    continue : Expr -> Parser (List Token) Expr
    parser   : Parser (List Token) (Operator 2, Expr)

    continue leftExpr =
      do
        state <- lift get
        case parse parser state of
          (_, Left _) => pure leftExpr
          (state', Right (op, rightExpr)) => do
            lift $ put state'
            continue (ExprOperator op [leftExpr, rightExpr])

    parser =
      do
        op <- opParser
        rhs <- lowerParser
        pure (op, rhs)

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

-- Idk what to do with this shit
dummyToken : TokenType -> Token
dummyToken tt = MkToken tt 0 0

tok0 : List Token
tok0 = map (dummyToken) [INTEGER 0, PLUS, INTEGER 2]

tok1 : List Token
tok1 = map (dummyToken) [MINUS, INTEGER 2]

tok2 : List Token
tok2 = map (dummyToken) [BANG, INTEGER 2]

tok3 : List Token
tok3 = map (dummyToken) []

tokUnary0 : List Token
tokUnary0 = map (dummyToken) [BANG, INTEGER 2]

tokUnary1 : List Token
tokUnary1 = map (dummyToken) [BANG, BANG, INTEGER 2]

tokUnary2 : List Token
tokUnary2 = map (dummyToken) [INTEGER 2]

tokUnary3 : List Token
tokUnary3 = map (dummyToken) [BANG, BANG]

tokFactor0 : List Token
tokFactor0 = map (dummyToken) [INTEGER 2, STAR, INTEGER 2]

tokFactor1 : List Token
tokFactor1 = map (dummyToken) [INTEGER 1, STAR, INTEGER 2, STAR, INTEGER 3]

tokFactor2 : List Token
tokFactor2 = map (dummyToken) [INTEGER 1, STAR, INTEGER 2, STAR, INTEGER 3, STAR, INTEGER 4]

tokFactor3 : List Token
tokFactor3 = map (dummyToken) [INTEGER 1, STAR]

tokFactor4 : List Token
tokFactor4 = map (dummyToken) [BANG, BANG, INTEGER 2, STAR, BANG, INTEGER 2]
