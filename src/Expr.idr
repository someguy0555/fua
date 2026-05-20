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

data ExprType : Type where
  TypeUnknown : ExprType
  TypeNil     : ExprType
  TypeBool    : ExprType
  TypeInt     : ExprType
  TypeReal    : ExprType
  TypeString  : ExprType
  TypeFunc    : List ExprType -> ExprType -> ExprType
  TypeTable   : (SortedMap Identifier ExprType) -> ExprType -- Mapping strings to types.

data Expr : Type where
  -- ExprUnassigned : ExprType -> Expr
  ExprOperand    : Show a => ExprType -> a -> Expr
  ExprVariable   : ExprType -> Identifier -> Expr
  ExprOperator   : ExprType -> Operator n -> Vect n Expr -> Expr
  ExprCall       : Expr -> List Expr -> Expr

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
Show ExprType where
  show TypeUnknown = "TypeUnknown"
  show TypeNil     = "TypeNil"
  show TypeBool    = "TypeBool"
  show TypeInt     = "TypeInt"
  show TypeReal    = "TypeReal"
  show TypeString  = "TypeString"
  show (TypeFunc arguments result) = show arguments ++ " -> " ++ show result
  -- show (TypeTable tbl)   = "TypeTable {" ++ show tbl ++ "}"
  show (TypeTable tbl)   = "TypeTable " ++ show tbl
  -- show (TypeTable tbl)   = "TypeTable { ... }"

covering -- Why is it not terminating??? I hate this language so much.
Eq ExprType where
  TypeUnknown == TypeUnknown = True
  TypeNil     == TypeNil     = True
  TypeBool    == TypeBool    = True
  TypeInt     == TypeInt     = True
  TypeReal    == TypeReal    = True
  TypeString  == TypeString  = True

  TypeFunc as r == TypeFunc as' r' =
    as == as' && r == r'

  -- TypeTable t == TypeTable t' =
  --   t == t'

  _ == _ = False

covering
Show Expr where
  -- show (ExprUnassigned ty) =
  --   "Unassigned : " ++ show ty

  show (ExprOperand ty val) =
    "Operand(" ++ show val ++ ") : " ++ show ty

  show (ExprVariable ty name) =
    "Variable(" ++ name ++ ") : " ++ show ty

  show (ExprOperator ty op exprs) =
    "Operator("
      ++ show op
      ++ ", "
      ++ show exprs
      ++ ") : "
      ++ show ty

  show (ExprCall fn args) =
    "Call("
      ++ show fn
      ++ ", "
      ++ show args
      ++ ")"

-- Show (Operator n) where
--   show _ = "Operator"

-- failing
--   Show Expr where
--     show (ExprOperand type a) = "..operand value.." ++ " : " ++ show type
--     show (ExprOperator type op exprs) = show op ++ show exprs ++ " : " ++ show type

expr0 : Expr
expr0 = ExprOperator TypeUnknown Add [ExprOperand TypeUnknown 2, ExprOperand TypeUnknown 2]

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
          -- left [ show x ++ show xs ]
        else left [ "parseOperator: token '" ++ (show x) ++ "' in '" ++ show tokens ++ "' does not fulfill predicate" ]

parseOperatorUsingTokenType : Operator n -> TokenType -> Parser (List Token) (Operator n)
parseOperatorUsingTokenType op tt =
  parserOverwriteError
    (modifyLastError (\txt => "Failed to parse operator using token type '" ++ show tt ++ "' in: " ++ txt))
    -- (\err => ["Failed to parse operator using token type '" ++ show tt ++ "'"])
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
          (_, Left _) =>
            pure leftExpr

          (state', Right (op, rightExpr)) =>
            do
              lift $ put state'

              let combined =
                    ExprOperator
                      TypeUnknown
                      op
                      [leftExpr, rightExpr]

              continue combined

    parser =
      do
        op <- opParser
        rhs <- lowerParser
        pure (op, rhs)

parsePrimary         : Parser (List Token) Expr
parsePrimaryWithCall : Parser (List Token) Expr
parseUnary           : Parser (List Token) Expr
parseExpr            : Parser (List Token) Expr
parseFactor          : Parser (List Token) Expr
parseTerm            : Parser (List Token) Expr
parseLogical         : Parser (List Token) Expr
parseComparison      : Parser (List Token) Expr
parseEquality        : Parser (List Token) Expr

parsePrimary =
      parseNumber
  <|> parseBooleanLiteral
  <|> parseNilLiteral
  <|> parseStringLiteral
  <|> parseIdentifier
  <|> parseParens
  --     (parserOverwriteError (\err => err ++ ["parseNumber     in parsePrimary failed"]) $ parseNumber )
  -- <|> (parserOverwriteError (\err => err ++ ["parseIdentifier in parsePrimary failed"]) $ parseIdentifier )
  -- <|> (parserOverwriteError (\err => err ++ ["parseParens     in parsePrimary failed"]) $ parseParens )
  where
    parseNumber =
      do
        MkToken tok _ _ <- parseToken isNumber
        pure $ case tok of
          INTEGER n => ExprOperand TypeInt n
          NUMBER r  => ExprOperand TypeReal r
          _         => ExprOperand TypeUnknown tok

    parseBooleanLiteral =
      do
        MkToken tok _ _ <- parseToken (isBooleanLiteral)
        pure $ case tok of
          TRUE  => ExprOperand TypeBool True
          FALSE => ExprOperand TypeBool True
          _     => ExprOperand TypeUnknown tok

    parseNilLiteral =
      do
        MkToken tok _ _ <- parseToken (isNilLiteral)
        pure $ case tok of
          NILV  => ExprOperand TypeNil ()
          _     => ExprOperand TypeUnknown tok

    parseStringLiteral =
      do
        MkToken tok _ _ <- parseToken isStringLiteral
        pure $ case tok of
          STRING s => ExprOperand TypeString s
          _        => ExprOperand TypeUnknown tok

    parseIdentifier =
      do
        MkToken tok _ _ <- parseToken isIdentifier
        pure $ case tok of
          IDENTIFIER s => ExprVariable TypeUnknown s
          _            => ExprOperand  TypeUnknown tok

    parseParens =
      do
        _ <- parseToken (isTokenType LEFT_PAREN)
        e <- parseExpr
        _ <- parseToken (isTokenType RIGHT_PAREN)
        pure e

parsePrimaryWithCall =
  do
    base <- parsePrimary
    parseCallChain base

  where
    parseCallChain : Expr -> Parser (List Token) Expr
    runCall : Parser (List Token) (List Expr)
    parseArgs : Parser (List Token) (List Expr)

    parseCallChain fn =
      do
        state <- lift get

        case parse runCall state of
          (_, Left _) =>
            pure fn

          (state', Right args) =>
            do
              lift $ put state'
              parseCallChain (ExprCall fn args)

    runCall =
      do
        _ <- parseToken (tokenTypeIs LEFT_PAREN)
        _ <- many parseLineEnd

        args <- parseArgs

        _ <- many parseLineEnd
        _ <- parseToken (tokenTypeIs RIGHT_PAREN)

        pure args

    -- parseArgs =
    --   many $
    --     do
    --       e <- parseExpr
    --       _ <- many parseLineEnd
    --       pure e

    optionalArg =
      (do e <- parseExpr; pure (Just e))
      <|> pure Nothing

    parseArgs =
      do
        first <- optionalArg
        case first of
          Nothing => pure []
          Just x =>
            do
              xs <- many (do _ <- parseToken (tokenTypeIs COMMA); parseExpr)
              pure (x :: xs)

-- parseUnary = parseBasic parser
--   where
--     parser : Parser (List Token) Expr
--     parser = do
--       oldState <- lift get
--       ?expr
parseUnary = parseBasic parser
  where
    opParser =
          parseOperatorUsingTokenType Not BANG
      <|> parseOperatorUsingTokenType Neg MINUS

    parser =
      (
        do
          state <- lift get
          op <- tryParse state $ opParser
          e  <- tryParse state $ parseUnary
          pure $ ExprOperator TypeUnknown op [e]
      )
      <|>
      parsePrimaryWithCall

-- Left-associative
parseFactor =
  parseLeftAssoc parseUnary opParser
  where
    opParser =
          parseOperatorUsingTokenType Mul STAR
      <|> parseOperatorUsingTokenType Div SLASH
      <|> parseOperatorUsingTokenType Mod PERCENT
-- parseFactor = parseBasic parser
--   where
--     opParser   =
--           parseOperatorUsingTokenType Mul STAR
--       <|> parseOperatorUsingTokenType Div SLASH
--       <|> parseOperatorUsingTokenType Mod PERCENT
--     parser =
--       (
--         do
--           state <- lift get
--           pre  <- tryParse state $ parseUnary
--           op   <- tryParse state $ opParser
--           post <- tryParse state $ parseFactor
--           pure $ ExprOperator TypeUnknown op [pre, post]
--       )
--       <|>
--       parseUnary
--       -- (parserOverwriteError (\err => err ++ ["parseUnary in parseFactor failed"]) $ parseUnary )

-- Left-associative
parseTerm =
  parseLeftAssoc parseFactor opParser
  where
    opParser =
          parseOperatorUsingTokenType Add PLUS
      <|> parseOperatorUsingTokenType Sub MINUS
-- parseTerm = parseBasic parser
--   where
--     opParser =
--           parseOperatorUsingTokenType Add PLUS
--       <|> parseOperatorUsingTokenType Sub MINUS
--
--     parser =
--       (
--         do
--           state <- lift get
--           pre  <- tryParse state $ parseFactor
--           op   <- tryParse state $ opParser
--           post <- tryParse state $ parseTerm
--           pure $ ExprOperator TypeUnknown op [pre, post]
--       )
--       <|> parseFactor
--       -- <|> (parserOverwriteError (\err => err ++ ["parseFactor in parseTerm failed"]) $ parseFactor )

-- Left-associative
parseLogical =
  parseLeftAssoc parseTerm opParser
  where
    opParser =
          parseOperatorUsingTokenType And AND
      <|> parseOperatorUsingTokenType Or OR
-- parseLogical = parseBasic parser
--   where
--     opParser =
--           parseOperatorUsingTokenType And AND
--       <|> parseOperatorUsingTokenType Or  OR
--
--     parser =
--       (
--         do
--           state <- lift get
--           pre  <- tryParse state $ parseTerm
--           op   <- tryParse state $ opParser
--           post <- tryParse state $ parseLogical
--           pure $ ExprOperator TypeUnknown op [pre, post]
--       )
--       <|>
--       parseTerm

-- Left-associative
parseComparison =
  parseLeftAssoc parseLogical opParser
  where
    opParser =
          parseOperatorUsingTokenType Greater GREATER
      <|> parseOperatorUsingTokenType GreaterEqual GREATER_EQUAL
      <|> parseOperatorUsingTokenType Less LESS
      <|> parseOperatorUsingTokenType LessEqual LESS_EQUAL
-- parseComparison = parseBasic parser
--   where
--     opParser =
--           parseOperatorUsingTokenType Greater      GREATER
--       <|> parseOperatorUsingTokenType GreaterEqual GREATER_EQUAL
--       <|> parseOperatorUsingTokenType Less         LESS
--       <|> parseOperatorUsingTokenType LessEqual    LESS_EQUAL
--
--     parser =
--       (
--         do
--           state <- lift get
--           pre  <- tryParse state $ parseLogical
--           op   <- tryParse state $ opParser
--           post <- tryParse state $ parseComparison
--           pure $ ExprOperator TypeUnknown op [pre, post]
--       )
--       <|>
--       parseLogical

-- Left-associative
parseEquality =
  parseLeftAssoc parseComparison opParser
  where
    opParser =
          parseOperatorUsingTokenType Equal EQUAL_EQUAL
      <|> parseOperatorUsingTokenType NotEqual BANG_EQUAL
-- parseEquality = parseBasic parser
--   where
--     opParser =
--           parseOperatorUsingTokenType Equal    EQUAL_EQUAL
--       <|> parseOperatorUsingTokenType NotEqual BANG_EQUAL
--
--     parser =
--       (
--         do
--           state <- lift get
--           pre  <- tryParse state $ parseComparison
--           op   <- tryParse state $ opParser
--           post <- tryParse state $ parseEquality
--           pure $ ExprOperator TypeUnknown op [pre, post]
--       )
--       <|>
--       parseComparison

parseExpr =
  parseEquality
  -- (parserOverwriteError (\err => err ++ ["parseEquality in parseExpr failed"]) $ parseEquality )

parseTokenAsPrimitiveType : (Token -> Bool) -> ExprType -> Parser (List Token) ExprType
parseTokenAsPrimitiveType predicate exprType =
  do
    tokens <- lift get
    case tokens of
      [] => left [ "No tokens found" ]
      (t::tt) =>
          if predicate t
            then do
              lift . put $ tt
              pure exprType
            else left [ "Token '" ++ show t ++ "' does not fit predicate" ]

  -- show TypeUnknown = "TypeUnknown"
  -- show TypeNil     = "TypeNil"
  -- show TypeBool    = "TypeBool"
  -- show TypeInt     = "TypeInt"
  -- show TypeReal    = "TypeReal"
  -- show TypeString  = "TypeString"
  -- show (TypeFunc arguments result) = show arguments ++ " -> " ++ show result
  -- -- show (TypeTable tbl)   = "TypeTable {" ++ show tbl ++ "}"
  -- show (TypeTable tbl)   = "TypeTable " ++ show tbl
-- Only able to process primitive types for now, not tables or functions or anything else.
parseExprType : Parser (List Token) ExprType
parseExprType =
      parseTokenAsPrimitiveType (isTokenType NILT   ) TypeNil
  <|> parseTokenAsPrimitiveType (isTokenType BOOL   ) TypeBool
  <|> parseTokenAsPrimitiveType (isTokenType INT    ) TypeInt
  <|> parseTokenAsPrimitiveType (isTokenType REAL   ) TypeReal
  <|> parseTokenAsPrimitiveType (isTokenType STRINGT) TypeString

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
