module Main

import Data.List
import Data.String
import Control.Monad.State
import Data.Either

import Debug.Trace

-- Utility functions
modifyLast : (a -> a) -> List a -> List a
modifyLast f [] = []
modifyLast f (x :: []) = f x :: []
modifyLast f (x :: (y :: xs)) = x :: (modifyLast f (y::xs))

digitToInt : Char -> Maybe Int
digitToInt '0' = Just 0
digitToInt '1' = Just 1
digitToInt '2' = Just 2
digitToInt '3' = Just 3
digitToInt '4' = Just 4
digitToInt '5' = Just 5
digitToInt '6' = Just 6
digitToInt '7' = Just 7
digitToInt '8' = Just 8
digitToInt '9' = Just 9
digitToInt _   = Nothing

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
  show (INTEGER i) = "{ " ++ "INTEGER: " ++ show i ++ " }"
  show (STRING s) = "{ " ++ "STRING: " ++ show s ++ " }"
  show _ = "{ TOKENTYPE }"

Show Token where
  show tk = "{" ++ show tk.line ++ ", " ++ show tk.column ++ ", " ++ show tk.token ++ "}"

Show ScannerError where
  show se = "{" ++ show se.line ++ ", " ++ show se.column ++ ", " ++ se.msg ++ "}"

Show a => Show (Cursor a) where
  show cur = show (cur.scanned, cur.left)

Show ScannerState where
  show se = "{" ++ show se.line ++ ", " ++ show se.column ++ ", " ++ show se.lines ++ ", " ++ show se.currLine ++ ", " ++ show se.tokens ++ "}"

Parser : Type -> Type -> Type -> Type
Parser parserState parserError = StateT parserState (Either parserError)

Scanner : Type -> Type
Scanner = Parser ScannerState ScannerError

peekChar : Scanner $ Maybe Char
peekChar = do
  state <- get
  pure $ case unpack state.currLine.left of
    [] =>
      do
        case state.lines.left of
          [] => Nothing
          left => do
            let trueLeft = unpack $ concat left
            case trueLeft of
              [] => Nothing
              x::_ => Just x
    ch::_ => Just ch

-- There appear to be no bugs here.
advance : Scanner $ Maybe Char
advance =
  do
    state <- get
    case unpack state.currLine.left of
      [] =>
        do
          case state.lines.left of
            [] => pure Nothing
            ln::linesLeft =>
              do
                put $ {
                  line     := state.line + 1,
                  column   := 0,
                  lines    := MkCursor (state.lines.scanned ++ [state.currLine.scanned]) linesLeft,
                  currLine := MkCursor "" ln
                } state
                advance
      ch::newLeft =>
        do
          put $ {
            column   := state.column + 1,
            currLine := MkCursor (state.currLine.scanned ++ (pack [ch])) (pack newLeft)
          } state
          pure $ Just ch

-- There appear to be no bugs here.
back : Scanner $ Maybe Char
back =
  do
    state <- get
    case unpack state.currLine.scanned of
      [] =>
        do
          case state.lines.scanned of
            [] => pure Nothing
            linesScanned@(_::_) =>
              do
                let lastScanned = last linesScanned
                let initScanned = init linesScanned
                put $ {
                  line     := state.line `minus` 1,
                  -- column   := length lastScanned,
                  column   := length lastScanned `minus` 1,
                  lines    := MkCursor initScanned $ (state.currLine.scanned ++ state.currLine.left) :: state.lines.left,
                  currLine := MkCursor lastScanned ""
                } state
                st2 <- get
                back
      lineScanned@(_::_) =>
        do
          let lastScanned = last lineScanned
          let initScanned = pack $ init lineScanned
          put $ {
            column   := state.column `minus` 1,
            currLine := MkCursor initScanned ((pack [lastScanned]) ++ state.currLine.left)
          } state
          pure $ Just lastScanned

match : Char -> Scanner Bool
match ch =
  do
    maybe <- peekChar 
    pure $ case maybe of
      Nothing => False
      Just peeked => if ch == peeked then True else False

isAtLineEnd : Scanner Bool
isAtLineEnd =
  do
    state <- get
    pure $ case unpack state.currLine.left of
      [] => False
      _  => True

addToken : TokenType -> Scanner ()
addToken tt =
  do
    state <- get
    put $ {
      tokens := state.tokens ++ [MkToken state.line state.column tt]
    } state

appendStringToTokenString : TokenType -> String -> TokenType
appendStringToTokenString (STRING str) app = STRING $ str ++ app
appendStringToTokenString _ app = STRING app 

appendExistingInteger : TokenType -> Integer -> TokenType
appendExistingInteger (INTEGER intg) i = INTEGER $ intg * 10 + i
appendExistingInteger _ i = INTEGER i

readStringLiteral : Scanner ()
readStringLiteral =
  do
    c <- advance
    state <- get
    case c of
      Nothing => pure ()
      -- Nothing => lift . Left $ MkScannerError state.line state.column "Unable to find string literal"
      Just '"' => do
        put $ { tokens := state.tokens ++ [ MkToken state.line state.column (STRING "") ] } state
        readStringLiteral'
      Just _ => pure ()
  where
    readStringLiteral' : Scanner ()
    readStringLiteral' =
      do
        mc <- advance
        state <- get
        case mc of
          Nothing => lift . Left $ MkScannerError state.line state.column "Unterminated string"
          Just c  =>
            do
              case c of
                '\\' => do
                  matches <- match '\\'
                  case matches of
                    True =>
                      do
                        _ <- advance
                        state <- get
                        put $ {
                          tokens := modifyLast (\tk => { token := appendStringToTokenString tk.token "\\" } tk) state.tokens
                        } state
                        readStringLiteral'
                    False => do
                      matches <- match '"'
                      case matches of
                        True =>
                          do
                            _ <- advance
                            state <- get
                            -- put $ { tokens := (\tk => appendStringToTokenString tk "\"" ) state.tokens } state
                            put $ {
                              tokens := modifyLast (\tk => { token := appendStringToTokenString tk.token "\"" } tk) state.tokens
                            } state
                            readStringLiteral'
                        False => readStringLiteral'
                '"' => pure ()
                c =>
                  do
                    -- put $ { tokens := (\tk => appendStringToTokenString tk (show c) ) state.tokens } state
                    put $ {
                      tokens := modifyLast (\tk => { token := appendStringToTokenString tk.token (pack [c]) } tk) state.tokens
                    } state
                    readStringLiteral'

readIntegerLiteral : Scanner ()
readIntegerLiteral =
  do
    mc <- advance
    case mc of
      Nothing => pure ()
      Just c => case digitToInt c of
        Nothing => pure ()
        Just d => do
          state <- get
          put $ {
            tokens := state.tokens ++ [ MkToken state.line state.column (INTEGER (the Integer $ cast d)) ]
          } state
          readIntegerLiteral'
  where
    readIntegerLiteral' : Scanner ()
    readIntegerLiteral' = do
      mc <- peekChar
      case mc of
        Nothing => pure ()
        Just c => case digitToInt c of
          Nothing => pure ()
          Just d => do
            _ <- advance
            state <- get
            put $ {
              tokens := modifyLast (\tk => { token := appendExistingInteger tk.token (the Integer $ cast d) } tk) state.tokens
            } state
            readIntegerLiteral'


scan' : Scanner $ List Token
scan' =
  do
    state <- get
    c <- advance
    case c of
      Nothing => pure state.tokens
      Just c => case c of
        '!' =>
          do
            r <- match '='
            case r of
              False => do
                addToken BANG
                scan'
              True => do
                _ <- advance
                addToken BANG_EQUAL
                scan'
        '=' =>
          do
            r <- match '='
            case r of
              False => do
                addToken EQUAL
                scan'
              True => do
                _ <- advance
                addToken EQUAL_EQUAL
                scan'
        '<' =>
          do
            r <- match '='
            case r of
              False => do
                addToken LESS
                scan'
              True => do
                _ <- advance
                addToken LESS_EQUAL
                scan'
        '>' =>
          do
            r <- match '='
            case r of
              False => do
                addToken GREATER
                scan'
              True => do
                _ <- advance
                addToken GREATER_EQUAL
                scan'
        '(' => do
          addToken LEFT_PAREN
          scan'
        ')' => do
          addToken RIGHT_PAREN
          scan'
        '{' => do
          addToken LEFT_BRACE
          scan'
        '}' => do
          addToken RIGHT_BRACE
          scan'
        ',' => do
          addToken COMMA
          scan'
        '.' => do
          addToken DOT
          scan'
        ';' => do
          addToken SEMICOLON
          scan'
        '+' => do
          addToken PLUS
          scan'
        '-' => do
          addToken MINUS
          scan'
        '*' => do
          addToken STAR
          scan'
        '/' => do
          addToken SLASH
          scan'
        '%' => do
          addToken PERCENT
          scan'
        ' '  => scan'
        '\r' => scan'
        '\t' => scan'
        '"' => do
          _ <- back
          _ <- readStringLiteral
          scan'
        ch => do
          if isDigit ch
             then do
               _ <- back
               _ <- readIntegerLiteral
               scan'
             else do
               lift . Left $ MkScannerError state.line state.column "Unexpected symbol"

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
        x::xs => MkCursor [] xs

main : IO ()
main = do
  putStrLn "Start:"
  code <- getLine
  case scan code of
       Left err => print err
       Right (st,t) => print t
