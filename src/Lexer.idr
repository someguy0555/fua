module Main

import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either
import Deriving.Show

import Debug.Trace
import System.File

import Parser
-- %language ElabReflection

record LexerState where
  constructor MkLexerState
  input  : String
  line   : Nat
  column : Nat

mkDummyLexerState input = MkLexerState input 0 0

-- This is a very temporary solution to the problem
-- It should be replaced with something else,
-- probably a foreign library.
data RealNumber = MkRealNumber Integer Integer
Show RealNumber where
  show (MkRealNumber a b) = show a ++ "." ++ show b
Eq RealNumber where
  (==) (MkRealNumber n1a n1b) (MkRealNumber n2a n2b) = n1a == n2a && n1b == n2b

data TokenType =
  -- Single character tokens
  LEFT_PAREN | RIGHT_PAREN | LEFT_BRACE | RIGHT_BRACE | LEFT_SQUARE | RIGHT_SQUARE |
  COMMA | COLON | SEMICOLON | PLUS | MINUS | SLASH | STAR | PERCENT |

  -- One or two character tokens
  BANG | BANG_EQUAL |
  EQUAL | EQUAL_EQUAL |
  GREATER | GREATER_EQUAL |
  LESS | LESS_EQUAL |
  DOT | DOT_DOT |

  -- Literals
  IDENTIFIER String | STRING String | INTEGER Integer | NUMBER RealNumber |

  -- Keywords
  IF | ELSE | WHILE | FOR | IN |
  FN | RETURN | -- PRINT |
  AND | OR |
  LET | CONST |
  NILT | BOOL | INT | REAL | STRINGT | -- Types
  NILV | TRUE | FALSE | -- Values
  BREAK |

  NEWLINE |

  EOF
  ;

-- This is so unbelievably ass..
Eq TokenType where
  (==) LEFT_PAREN LEFT_PAREN = True
  (==) RIGHT_PAREN RIGHT_PAREN = True
  (==) LEFT_BRACE LEFT_BRACE = True
  (==) RIGHT_BRACE RIGHT_BRACE = True
  (==) LEFT_SQUARE LEFT_SQUARE = True
  (==) RIGHT_SQUARE RIGHT_SQUARE = True
  (==) COMMA COMMA = True
  (==) COLON COLON = True
  (==) SEMICOLON SEMICOLON = True
  (==) PLUS PLUS = True
  (==) MINUS MINUS = True
  (==) SLASH SLASH = True
  (==) STAR STAR = True
  (==) PERCENT PERCENT = True
  (==) BANG BANG = True
  (==) BANG_EQUAL BANG_EQUAL = True
  (==) EQUAL EQUAL = True
  (==) EQUAL_EQUAL EQUAL_EQUAL = True
  (==) GREATER GREATER = True
  (==) GREATER_EQUAL GREATER_EQUAL = True
  (==) LESS LESS = True
  (==) LESS_EQUAL LESS_EQUAL = True
  (==) DOT DOT = True
  (==) DOT_DOT DOT_DOT = True
  (==) (IDENTIFIER s1) (IDENTIFIER s2) = s1 == s2
  (==) (STRING s1) (STRING s2) = s1 == s2
  (==) (INTEGER n1) (INTEGER n2) = n1 == n2
  (==) (NUMBER r1) (NUMBER r2) = r1 == r2
  (==) IF IF = True
  (==) ELSE ELSE = True
  (==) WHILE WHILE = True
  (==) FOR FOR = True
  (==) IN IN = True
  (==) FN FN = True
  (==) RETURN RETURN = True
  -- (==) PRINT PRINT = True
  (==) AND AND = True
  (==) OR OR = True
  (==) LET LET = True
  (==) CONST CONST = True
  (==) NILT NILT = True
  (==) BOOL BOOL = True
  -- (==) CHAR CHAR = True
  (==) INT INT = True
  (==) REAL REAL = True
  (==) STRINGT STRINGT = True
  (==) NILV NILV = True
  (==) TRUE TRUE = True
  (==) FALSE FALSE = True
  (==) BREAK BREAK = True
  (==) NEWLINE NEWLINE = True
  (==) EOF EOF = True
  (==) _ _ = False

-- tokenTypeShow : Show TokenType
-- tokenTypeShow = %runElab derive

Show TokenType where
  show LEFT_PAREN = "LEFT_PAREN"
  show RIGHT_PAREN = "RIGHT_PAREN"
  show LEFT_BRACE = "LEFT_BRACE"
  show RIGHT_BRACE = "RIGHT_BRACE"
  show LEFT_SQUARE = "LEFT_SQUARE"
  show RIGHT_SQUARE = "RIGHT_SQUARE"
  show COMMA = "COMMA"
  show COLON = "COLON"
  show SEMICOLON = "SEMICOLON"
  show PLUS = "PLUS"
  show MINUS = "MINUS"
  show SLASH = "SLASH"
  show STAR = "STAR"
  show PERCENT = "PERCENT"
  show BANG = "BANG"
  show BANG_EQUAL = "BANG_EQUAL"
  show EQUAL = "EQUAL"
  show EQUAL_EQUAL = "EQUAL_EQUAL"
  show GREATER = "GREATER"
  show GREATER_EQUAL = "GREATER_EQUAL"
  show LESS = "LESS"
  show LESS_EQUAL = "LESS_EQUAL"
  show DOT = "DOT"
  show DOT_DOT = "DOT_DOT"

  show (IDENTIFIER s) = "IDENTIFIER " ++ show s
  show (STRING s)     = "STRING " ++ show s
  show (INTEGER n)    = "INTEGER " ++ show n
  show (NUMBER r)     = "NUMBER " ++ show r

  show IF = "IF"
  show ELSE = "ELSE"
  show WHILE = "WHILE"
  show FOR = "FOR"
  show IN = "IN"
  show FN = "FN"
  show RETURN = "RETURN"
  -- show PRINT = "PRINT"
  show AND = "AND"
  show OR = "OR"
  show LET = "LET"
  show CONST = "CONST"
  show NILT = "NILT"
  show BOOL = "BOOL"
  -- show CHAR = "CHAR"
  show INT = "INT"
  show REAL = "REAL"
  show STRINGT = "STRINGT"
  show NILV = "NILV"
  show TRUE = "TRUE"
  show FALSE = "FALSE"
  show BREAK = "BREAK"

  show NEWLINE = "NEWLINE"
  show EOF = "EOF"

record Token where
  constructor MkToken
  token  : TokenType
  line   : Nat
  column : Nat

Show Token where
  show (MkToken token line column) = "{ token = " ++ show token ++ ", line = " ++ show line ++ ", column = " ++ show column ++ "}"

isChar : Char -> Bool
isChar = isAlpha

isTokenType : TokenType -> Token -> Bool
isTokenType tt tk = if tk.token == tt then True else False

parseChar : ( Char -> Bool ) -> Parser LexerState Char
parseChar predicate =
  do
   MkLexerState input line column <- lift get
   case unpack input of
       [] => left [ "No character found" ]
       (h::t) =>
         if predicate h
           then do
             -- let (newLine, newCol) = if h == '\n' then (line + 1, 0) else (line, column + 1) -- This is a bit hacky imo..
             -- lift . put $ MkLexerState ( pack t ) newLine newCol
             lift . put $ MkLexerState ( pack t ) line ( column + 1)
             pure h
             else left [ "Character '" ++ show h ++ "' does not match given predicate" ]

parseSpecificChar : Char -> Parser LexerState Char
parseSpecificChar chr = parseChar (chr==)

parseKeyword : TokenType -> String -> Parser LexerState Token
parseKeyword tt prf =
  do
    MkLexerState input line column <- lift get
    if prf `isPrefixOf` input
       then do
         let prefixLen = length prf
         lift . put $ MkLexerState ( pack . drop prefixLen . unpack $ input ) line ( column + prefixLen )
         pure $ MkToken tt line column
       else left [ "Keyword '" ++ prf ++ "' not found" ]

parseInteger : Parser LexerState Integer
parseInteger =
  do
    state <- lift get
    case (parse . some $ parseChar (isDigit) ) state of
      (_, Left err) => left [ "Expected to find atleast one digit in integer" ]
      (state', Right rh) => do
        lift . put $ state'
        pure . charsToInts $ rh
  where
    toDigit : Char -> Int
    toDigit '0' = 0
    toDigit '1' = 1
    toDigit '2' = 2
    toDigit '3' = 3
    toDigit '4' = 4
    toDigit '5' = 5
    toDigit '6' = 6
    toDigit '7' = 7
    toDigit '8' = 8
    toDigit '9' = 9
    toDigit  _  = 0
    charsToInts : List Char -> Integer
    charsToInts = cast . foldl (\a, b => a * 10 + toDigit b) 0


parseIntegerLiteral : Parser LexerState Token
parseIntegerLiteral =
  do
    state@(MkLexerState _ line column) <- lift get
    case (parse parseInteger) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (INTEGER rh) line column

parseEscapedChar : ( Char -> Bool) -> Parser LexerState Char
parseEscapedChar predicate =
  do
    state <- lift get
    let parser = (\_, ch => ch) <$> parseChar (=='\\') <*> parseChar predicate
    case (parse parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

parseInsideStringLiteral : Parser LexerState String
parseInsideStringLiteral =
  do
    state <- lift get
    let parser = many $ parseEscapedChar (isChar) <|> parseChar (isChar) -- In progress
    -- let parser = parseChar (isChar) -- In progress
    case (parse $ parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure . pack $ rh

replaceLastEl : (a -> a) -> List a -> List a
replaceLastEl func [] = []
replaceLastEl func ls@(_::_) = ini ++ [func lst]
  where
    ini = init ls
    lst = last ls

modifyLastError : (String -> String) -> ErrorMsg -> ErrorMsg
modifyLastError func = replaceLastEl func

parseStringLiteral : Parser LexerState Token
parseStringLiteral =
  do
    state@(MkLexerState _ line column) <- lift get
    let firstQuoteParser    = parserOverwriteError (\err => [ "No start to string literal found" ] ) $ parseChar ('"'==)
    let lastQuoteParser     = parserOverwriteError (\err => [ "No end to string literal found"   ] ) $ parseChar ('"'==)
    let stringLiteralParser = parserOverwriteError (modifyLastError (\err' => "Inside string literal: " ++ err')) $ parseInsideStringLiteral
    let parser = (\_, str, _ => str) <$> firstQuoteParser <*> stringLiteralParser <*> lastQuoteParser
    case (parse parser) state of 
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (STRING rh) line column

parseIdentifier : Parser LexerState Token
parseIdentifier =
  do
    state@(MkLexerState _ line column) <- lift get
    let parser = (\hd, tl => pack $ hd::tl) <$> parseChar (isIdentifierHead) <*> (many $ parseChar (isIdentifierTail))
    case (parse parser) state of
      -- (_, Left err) => left "In identifier: " ++ err
      (_, Left []) => left [ "Unknow error in parseIdentifier" ]
      (_, Left err@(_::_)) => left $ (init err) ++ [ ("In identifier: " ++ last err) ]
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (IDENTIFIER rh) line column
  where
    isIdentifierHead : Char -> Bool
    isIdentifierHead '_' = True
    isIdentifierHead chr = isAlpha chr
    -- isIdentifierHead '_' = trace ("TRACE HEAD: " ++ show '_') $ True
    -- isIdentifierHead chr = trace ("TRACE HEAD: " ++ show chr) $ isAlpha chr
    isIdentifierTail : Char -> Bool
    isIdentifierTail chr = isAlpha chr || isDigit chr

parseRealNumberLiteral : Parser LexerState Token
parseRealNumberLiteral =
  do
    state@(MkLexerState _ line column) <- lift get
    let parser = (\pre, _, post => MkRealNumber pre post) <$> parseInteger <*> parseChar ('.'==) <*> parseInteger
    case (parse parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure $ MkToken (NUMBER rh) line column

parseWhiteSpace : Parser LexerState ()
parseWhiteSpace =
  do
    _ <- many $ parseChar (isPureSpace)
    pure ()
  -- do
  --   state <- lift get
  --   let parser = many . parseChar $ (isPureSpace)
  --   case (parse parser) state of
  --     (_, Left err) => left err
  --     (state', Right rh) => do
  --       lift . put $ state'
  --       pure . pack $ rh
  where
    isPureSpace : Char -> Bool
    isPureSpace c = ( isSpace c ) && ( not . isNL $ c )

parseNewLine : Parser LexerState Token
parseNewLine =
  do
    state@(MkLexerState _ line column) <- lift get
    let parser = parseChar (isNL)
    case (parse parser) state of
      (_, Left err) => left err
      (MkLexerState input line' _, Right rh) => do
        lift . put $ MkLexerState input ( line + 1 ) 0
        pure $ MkToken NEWLINE line column

parseMultipleCharacterTokens : Parser LexerState Token
parseMultipleCharacterTokens = parseBasic parser
  where
    parser : Parser LexerState Token
    parser =
          parseKeyword BANG_EQUAL    "!="
      <|> parseKeyword EQUAL_EQUAL   "=="
      <|> parseKeyword GREATER_EQUAL ">="
      <|> parseKeyword LESS_EQUAL    "<="
      <|> parseKeyword LESS_EQUAL    ".."

parseSingleCharacterTokens : Parser LexerState Token
parseSingleCharacterTokens = parseBasic parser
  where
    parser : Parser LexerState Token
    parser =
          parseKeyword LEFT_PAREN   "("
      <|> parseKeyword RIGHT_PAREN  ")"
      <|> parseKeyword LEFT_BRACE   "{"
      <|> parseKeyword RIGHT_BRACE  "}"
      <|> parseKeyword LEFT_SQUARE  "["
      <|> parseKeyword RIGHT_SQUARE "]"
      <|> parseKeyword COMMA        ","
      <|> parseKeyword DOT          "."
      <|> parseKeyword COLON        ":"
      <|> parseKeyword SEMICOLON    ";"
      <|> parseKeyword PLUS         "+"
      <|> parseKeyword MINUS        "-"
      <|> parseKeyword SLASH        "/"
      <|> parseKeyword STAR         "*"
      <|> parseKeyword PERCENT      "%"
      <|> parseKeyword BANG         "!"
      <|> parseKeyword EQUAL        "="
      <|> parseKeyword GREATER      ">"
      <|> parseKeyword LESS         "<"

parseKeywordTokens : Parser LexerState Token
parseKeywordTokens = parseBasic parser
  where
    parser : Parser LexerState Token
    parser =
          parseKeyword IF      "if"
      <|> parseKeyword ELSE    "else"
      <|> parseKeyword WHILE   "while"
      <|> parseKeyword FOR     "for"
      <|> parseKeyword IN      "in"
      <|> parseKeyword FN      "fn"
      <|> parseKeyword RETURN  "return"
      -- <|> parseKeyword PRINT   "print"
      <|> parseKeyword AND     "and"
      <|> parseKeyword OR      "or"
      <|> parseKeyword LET     "let"
      <|> parseKeyword CONST   "const"
      <|> parseKeyword NILT    "Nil"
      <|> parseKeyword BOOL    "Bool"
      -- <|> parseKeyword CHAR "Char"
      <|> parseKeyword INT     "Int"
      <|> parseKeyword REAL    "Real"
      <|> parseKeyword STRINGT "String"
      <|> parseKeyword NILV    "nil"
      <|> parseKeyword TRUE    "true"
      <|> parseKeyword FALSE   "false"
      <|> parseKeyword BREAK   "break"

lexToken : Parser LexerState Token
lexToken = -- parserOverwriteError (\err => "Unable to parse txt") $
      parseNewLine
  <|> parseKeywordTokens
  <|> parseMultipleCharacterTokens
  <|> parseSingleCharacterTokens
  <|> parseIdentifier
  <|> parseStringLiteral
  <|> parseIntegerLiteral
  <|> parseRealNumberLiteral

lexTokens : Parser LexerState (List Token)
lexTokens = many lexToken

parseText : Parser LexerState a -> String -> (LexerState, Either ErrorMsg a)
parseText p str = runState (MkLexerState str 0 0) (runEitherT p)

lexer : Parser LexerState (List Token)
lexer = many lexer'
  where
    lexer' =
      do
        _ <- parseWhiteSpace
        tok <- lexToken
        pure tok

-- lexer : (LexerState, List Token) -> (LexerState, List Token, ErrorMsg)
-- lexer (state, ls) =
--   case parse parser state of
--     (state', Right rh) => lexer (state', (rh::ls))
--     (state', Left err') => (state', reverse ls, err')
--   where
--     parser' : Parser LexerState Token
--     parser' = -- parserOverwriteError (\err => "Unable to parse txt") $
--           parseNewLine
--       <|> parseKeywordTokens
--       <|> parseMultipleCharacterTokens
--       <|> parseSingleCharacterTokens
--       <|> parseIdentifier
--       <|> parseStringLiteral
--       <|> parseIntegerLiteral
--       <|> parseRealNumberLiteral
--     parser : Parser LexerState Token
--     parser = 
--       do
--         state <- lift get
--         case (parse parseWhiteSpace) state of
--           (_, Left _) => left [ "Unknown error" ]
--           (state', Right rh) => do
--             lift . put $ state'
--             case (parse parser') state' of
--               (_, Left err) => left err
--               (state', Right rh) => do
--                 lift . put $ state'
--                 pure rh
