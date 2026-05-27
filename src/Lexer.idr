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

data TokenType =
  -- Single character tokens
  LEFT_PAREN | RIGHT_PAREN |
  COLON | PLUS | MINUS | SLASH | STAR | PERCENT |
  AMPERSAND | PIPE |

  -- One or two character tokens
  BANG | BANG_EQUAL |
  EQUAL | EQUAL_EQUAL |
  GREATER | GREATER_EQUAL |
  LESS | LESS_EQUAL |

  IDENTIFIER String | INTEGER Integer |

  -- Keywords
  IF | THEN | GOTO | PRINT |

  NEWLINE |

  EOF
  ;

Show TokenType where
  show LEFT_PAREN = "("
  show RIGHT_PAREN = ")"
  show COLON = ":"
  show PLUS = "+"
  show MINUS = "-"
  show SLASH = "/"
  show STAR = "*"
  show PERCENT = "%"
  show AMPERSAND = "&"
  show PIPE = "|"

  show BANG = "!"
  show BANG_EQUAL = "!="
  show EQUAL = "="
  show EQUAL_EQUAL = "=="
  show GREATER = ">"
  show GREATER_EQUAL = ">="
  show LESS = "<"
  show LESS_EQUAL = "<="

  show (IDENTIFIER s) = "IDENTIFIER(" ++ s ++ ")"
  show (INTEGER n) = "INTEGER(" ++ show n ++ ")"

  show IF = "if"
  show THEN = "then"
  show GOTO = "goto"
  show PRINT = "print"

  show NEWLINE = "\\n"
  show EOF = "EOF"

Eq TokenType where
  (==) LEFT_PAREN LEFT_PAREN = True
  (==) RIGHT_PAREN RIGHT_PAREN = True
  (==) COLON COLON = True
  (==) PLUS PLUS = True
  (==) MINUS MINUS = True
  (==) SLASH SLASH = True
  (==) STAR STAR = True
  (==) PERCENT PERCENT = True
  (==) AMPERSAND AMPERSAND = True
  (==) PIPE PIPE = True


  (==) BANG BANG = True
  (==) BANG_EQUAL BANG_EQUAL = True
  (==) EQUAL EQUAL = True
  (==) EQUAL_EQUAL EQUAL_EQUAL = True
  (==) GREATER GREATER = True
  (==) GREATER_EQUAL GREATER_EQUAL = True
  (==) LESS LESS = True
  (==) LESS_EQUAL LESS_EQUAL = True

  (==) (IDENTIFIER a) (IDENTIFIER b) = a == b
  (==) (INTEGER a) (INTEGER b) = a == b

  (==) IF IF = True
  (==) THEN THEN = True
  (==) GOTO GOTO = True
  (==) PRINT PRINT = True

  (==) NEWLINE NEWLINE = True
  (==) EOF EOF = True

  (==) _ _ = False

public export
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
    isIdentifierHead chr = isAlpha chr || (chr == '_')
    -- isIdentifierHead '_' = trace ("TRACE HEAD: " ++ show '_') $ True
    -- isIdentifierHead chr = trace ("TRACE HEAD: " ++ show chr) $ isAlpha chr
    isIdentifierTail : Char -> Bool
    isIdentifierTail chr = isAlpha chr || isDigit chr || (chr == '_')

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
          parseKeyword BANG_EQUAL             "!="
      <|> parseKeyword EQUAL_EQUAL            "=="
      <|> parseKeyword GREATER_EQUAL          ">="
      <|> parseKeyword LESS_EQUAL             "<="
      <|> parseKeyword LESS_EQUAL             ".."

parseSingleCharacterTokens : Parser LexerState Token
parseSingleCharacterTokens = parseBasic parser
  where
    parser : Parser LexerState Token
    parser =
          parseKeyword LEFT_PAREN   "("
      <|> parseKeyword RIGHT_PAREN  ")"
      <|> parseKeyword COLON        ":"
      <|> parseKeyword PLUS         "+"
      <|> parseKeyword MINUS        "-"
      <|> parseKeyword SLASH        "/"
      <|> parseKeyword STAR         "*"
      <|> parseKeyword PERCENT      "%"
      <|> parseKeyword BANG         "!"
      <|> parseKeyword EQUAL        "="
      <|> parseKeyword GREATER      ">"
      <|> parseKeyword LESS         "<"
      <|> parseKeyword AMPERSAND    "&"
      <|> parseKeyword PIPE         "|"

parseKeywordTokens : Parser LexerState Token
parseKeywordTokens = parseBasic parser
  where
    parser : Parser LexerState Token
    parser =
          parseKeyword IF      "if"
      <|> parseKeyword THEN    "then"
      <|> parseKeyword GOTO    "goto"
      <|> parseKeyword PRINT   "print"

lexToken : Parser LexerState Token
lexToken = -- parserOverwriteError (\err => "Unable to parse txt") $
      parseNewLine
  <|> parseKeywordTokens
  <|> parseMultipleCharacterTokens
  <|> parseSingleCharacterTokens
  <|> parseIdentifier
  <|> parseIntegerLiteral

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
