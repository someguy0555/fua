module Main

import Data.List;
import Data.String;
import Control.Monad.State;
import Data.Either;

import Debug.Trace;

-- Utility functions
modifyLast : (a -> a) -> List a -> List a
modifyLast f [] = []
modifyLast f (x :: []) = f x :: []
modifyLast f (x :: (y :: xs)) = modifyLast f (y::xs)

data TokenType =
  -- Single character tokens
  LEFT_PAREN | RIGHT_PAREN | LEFT_BRACE | RIGHT_BRACE |
  COMMA | DOT | PLUS | MINUS | SEMICOLON | SLASH | STAR |

  -- One or two character tokens
  BANG | BANG_EQUAL |
  EQUAL | EQUAL_EQUAL |
  GREATER | GREATER_EQUAL |
  LESS | LESS_EQUAL |

  -- Literals
  IDENTIFIER String | STRING String | INTEGER Integer | NUMBER Integer |

  -- Keywords
  IF | ELSE | WHILE | FOR | IN |
  RETURN | PRINT |
  AND | OR |

  EOF
  ;

record Token where
  constructor MkToken
  line : Nat
  column : Nat
  token : TokenType

record ScannerError where
  constructor MkScannerError
  line : Nat
  column : Nat
  msg : String

record Cursor a where
  constructor MkCursor
  scanned : a
  left : a

record ScannerState where
  constructor MkScannerState
  line : Nat
  column : Nat
  lines : Cursor (List String) -- lines above the current one, lines below the current one.
  currLine : Cursor String     -- left of the cursor, right of the cursor
  tokens : List Token

Show TokenType where
  show t = "TOKENTYPE"

Show Token where
  show tk = "{" ++ show tk.line ++ ", " ++ show tk.column ++ ", " ++ show tk.token ++ "}"

Show ScannerError where
  show se = "{" ++ show se.line ++ ", " ++ show se.column ++ ", " ++ se.msg ++ "}"

Parser : Type -> Type -> Type -> Type
Parser parserState parserError = StateT parserState (Either parserError)

Scanner : Type -> Type
Scanner = Parser ScannerState ScannerError

appendStringToTokenString : TokenType -> String -> TokenType
appendStringToTokenString (STRING str) app = STRING $ str ++ app
appendStringToTokenString _ app = STRING app 

-- peekChar : Scanner $ Maybe Char
-- peekChar = do
--   state <- get
--
-- advance : Scanner $ Char
-- match : Char -> Scanner Bool
-- isAtLineEnd : Scanner Bool

||| Takes a bunch of lines of code, and scans them into tokens.
scan' : Scanner $ List Token
scan' =
  do
    state <- get
    case unpack $ state.currLine.left of
      [] =>
        do
          case state.lines.left of
            [] => pure state.tokens
            nextLine::newLeft =>
              do
                let lines = state.lines
                let currLine = state.currLine
                put $ {
                  line     := state.line + 1,
                  column   := 0,
                  lines    := MkCursor (lines.scanned ++ [currLine.scanned ++ currLine.left]) newLeft,
                  currLine := MkCursor "" nextLine
                } state
                scan'
      old@('!'::'='::new) => addToken old new BANG_EQUAL
      old@('='::'='::new) => addToken old new EQUAL_EQUAL
      old@('<'::'='::new) => addToken old new LESS_EQUAL
      old@('>'::'='::new) => addToken old new GREATER_EQUAL
      old@('('::new)      => addToken old new LEFT_PAREN
      old@(')'::new)      => addToken old new RIGHT_PAREN
      old@('{'::new)      => addToken old new LEFT_BRACE
      old@('}'::new)      => addToken old new RIGHT_BRACE
      old@(','::new)      => addToken old new COMMA
      old@('.'::new)      => addToken old new DOT
      old@('-'::new)      => addToken old new MINUS
      old@('+'::new)      => addToken old new PLUS
      old@(';'::new)      => addToken old new SEMICOLON
      old@('*'::new)      => addToken old new LEFT_PAREN
      old@(' '::new)      => skip old new
      old@('\r'::new)     => skip old new
      old@('\t'::new)     => skip old new
      old@('"'::new)      => addStringLiteral new
      _ => lift . Left $ MkScannerError state.line state.column "Unexpected symbol"
  where
    ||| Takes the old left String, the new left String, the TokenType, 
    ||| and moves the "cursor" to the right by the size of the taken character(s).
    addToken : List Char -> List Char -> TokenType -> Scanner $ List Token
    addToken old new tt =
      do
        state <- get
        let currLine = state.currLine
        let skipNum = length old `minus` length new
        let taken = pack . take skipNum $ old 
        put $ {
          column   := state.column + skipNum,
          currLine := MkCursor (currLine.scanned ++ taken) (pack new),
          tokens   := state.tokens ++ [MkToken state.line state.column tt] -- NOTE: I'm not sure this works like I'd expect it to...
        } state
        scan'
    ||| Skip this character
    skip : List Char -> List Char -> Scanner $ List Token
    skip old new =
      do
        state <- get
        let currLine = state.currLine
        let skipNum = length old `minus` length new
        let taken = pack . take skipNum $ old 
        put $ {
          column   := state.column + skipNum,
          currLine := MkCursor (currLine.scanned ++ taken) (pack new)
        } state
        scan'

    ||| Is at end of current line
    scanTillLiteralEnd : Scanner $ List Token
    scanTillLiteralEnd =
      do
        state <- get
        case unpack $ traceVal state.currLine.left of
             [] => lift . Left $ MkScannerError state.line state.column "Unterminated string"
             '\\'::'\\'::'"'::xs => pushToken 2 "\\\\" "\\" (pack xs)
             '\\'::'"'::xs       => pushToken 2 "\\\"" "\"" (pack xs)
             '"'::xs             =>
              do
               tokens <- pushToken 1 "\"" "" (pack xs)
               trace (show tokens) scan'
             x::xs               => pushToken 1 (show x) (show x) (pack xs)
      where
          pushToken : Nat -> String -> String -> String -> Scanner $ List Token
          pushToken pushChars skipStr tokenStr newLeft =
            do
               state <- get
               put $ {
                 column   := state.column + pushChars,
                 currLine := MkCursor (state.currLine.scanned ++ skipStr) newLeft,
                 tokens   := modifyLast (\tk => { token := appendStringToTokenString tk.token tokenStr } tk) state.tokens
               } state
               scanTillLiteralEnd

    ||| Scan and add string literal
    addStringLiteral : List Char -> Scanner $ List Token
    addStringLiteral new =
      do
        state <- get
        put $ {
          column   := state.column + 1,
          currLine := MkCursor (state.currLine.scanned ++ "\"") (pack new),
          tokens   := state.tokens ++ [MkToken state.line state.column (STRING "")] -- NOTE: I'm not sure this works like I'd expect it to...
        } state
        _ <- scanTillLiteralEnd
        scan'

scan : String -> Either ScannerError (ScannerState, List Token)
scan code = runStateT (MkScannerState 0 0 allLines (MkCursor "" currLine) []) scan'
  where
    currLine : String
    currLine =
      case Data.String.lines code of
        []   => ""
        x::_ => x
    allLines : Cursor $ List String
    allLines =
      case lines code of
        []    => MkCursor [] []
        x::xs => MkCursor [x] xs

main : IO ()
main = do
  putStrLn "Start:"
  code <- getLine
  case scan code of
       Left err => print err
       Right (st,t) => print t
