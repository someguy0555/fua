module Main

import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Debug.Trace
import System.File

import Parser

-- This is a very temporary solution to the problem
-- It should be replaced with something else,
-- probably a foreign library.
data RealNumber = MkRealNumber Integer Integer
Show RealNumber where
  show (MkRealNumber a b) = show a ++ "." ++ show b

data TokenType =
  -- Single character tokens
  LEFT_PAREN | RIGHT_PAREN | LEFT_BRACE | RIGHT_BRACE |
  COMMA | DOT | SEMICOLON | PLUS | MINUS | SLASH | STAR | PERCENT |

  -- One or two character tokens
  BANG | BANG_EQUAL |
  EQUAL | EQUAL_EQUAL |
  GREATER | GREATER_EQUAL |
  LESS | LESS_EQUAL |

  -- Literals
  IDENTIFIER String | STRING String | INTEGER Integer | NUMBER RealNumber |

  -- Keywords
  IF | ELSE | WHILE | FOR | IN |
  RETURN | PRINT |
  AND | OR |
  LET | CONST |

  EOF
  ;

record Token where
  constructor MkToken
  token  : TokenType
  line   : Nat
  column : Nat

isChar : Char -> Bool
isChar = isAlpha

parseChar : ( Char -> Bool ) -> Parser Char
parseChar predicate =
  do
   MkParserState input line column <- lift get
   case unpack input of
       [] => left "No character that matches the predicate found"
       (h::t) =>
         if predicate h
           then do
             lift . put $ MkParserState ( pack t ) line ( column + 1 )
             pure h
           else left $ "Character '" ++ show h ++ "' is not alpha"

parseKeyword : TokenType -> String -> Parser Token
parseKeyword tt prf =
  do
    MkParserState input line column <- lift get
    if prf `isPrefixOf` input
       then do
         let prefixLen = length prf
         lift . put $ MkParserState ( pack . drop prefixLen . unpack $ input ) line ( column + prefixLen )
         pure $ MkToken tt line ( column + prefixLen )
       else left $ "Keyword '" ++ prf ++ "' not found"

parseInteger : Parser Integer
parseInteger =
  do
    state <- lift get
    case (parse . some $ parseChar (isDigit) ) state of
      (_, Left err) => left "Expected to find atleast one digit in integer"
      (state', Right rh) => do
        lift . put $ state'
        pure . charsToInts $ rh
  where
    charsToInts : List Char -> Integer
    charsToInts = cast . foldl (\a, b => a * 10 + cast b) 0

parseIntegerLiteral : Parser Token
parseIntegerLiteral =
  do
    state@(MkParserState _ line column) <- lift get
    case (parse parseInteger) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (INTEGER rh) line column

parseEscapedChar : ( Char -> Bool) -> Parser Char
parseEscapedChar predicate =
  do
    state <- lift get
    let parser = (\_, ch => ch) <$> parseChar (=='\\') <*> parseChar predicate
    case (parse parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

parseInsideStringLiteral : Parser String
parseInsideStringLiteral =
  do
    state <- lift get
    let parser = many $ parseEscapedChar (isChar) <|> parseChar (isChar)
    case (parse $ parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure . pack $ rh

parseStringLiteral : Parser Token
parseStringLiteral =
  do
    state@(MkParserState _ line column) <- lift get
    let firstQuoteParser = parserOverwriteError (\err => "No start to string literal found") $ parseChar ('"'==)
    let lastQuoteParser  = parserOverwriteError (\err => "No end to string literal found" ) $ parseChar ('"'==)
    let stringLiteralParser = parserOverwriteError (\err => "Inside string literal: " ++ err) $ parseInsideStringLiteral
    let parser = (\_, str, _ => str) <$> firstQuoteParser <*> stringLiteralParser <*> lastQuoteParser
    case (parse parser) state of 
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (STRING rh) line column

parseIdentifier : Parser Token
parseIdentifier =
  do
    state@(MkParserState _ line column) <- lift get
    let parser = (\hd, tl => pack $ hd::tl) <$> parseChar (isIdentifierHead) <*> (some $ parseChar (isIdentifierTail))
    case (parse parser) state of
      (_, Left err) => left $ "In identifier: " ++ err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (IDENTIFIER rh) line column
  where
    isIdentifierHead : Char -> Bool
    isIdentifierHead '_' = True
    isIdentifierHead chr = isAlpha chr
    isIdentifierTail : Char -> Bool
    isIdentifierTail chr = isAlpha chr || isDigit chr

parseRealNumberLiteral : Parser Token
parseRealNumberLiteral =
  do
    state@(MkParserState _ line column) <- lift get
    let parser = (\pre, _, post => MkRealNumber pre post) <$> parseInteger <*> parseChar ('.'==) <*> parseInteger
    case (parse parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (NUMBER rh) line column

