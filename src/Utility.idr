module Main

import Data.List
import Data.SortedMap
import Data.Vect
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Parser
import Lexer

isLineEnd : TokenType -> Bool
isLineEnd tt = tt == NEWLINE || tt == SEMICOLON

tokenTypeIs : TokenType -> Token -> Bool
tokenTypeIs tt (MkToken tok _ _) = tt == tok

isIntegerToken : Token -> Bool
isIntegerToken (MkToken (INTEGER _) _ _) = True
isIntegerToken _ = False

isRealNumberToken : Token -> Bool
isRealNumberToken (MkToken (NUMBER  _) _ _) = True
isRealNumberToken _ = False

isNumber : Token -> Bool
isNumber tk = isIntegerToken tk || isRealNumberToken tk

isBooleanLiteral : Token -> Bool
isBooleanLiteral (MkToken TRUE  _ _) = True
isBooleanLiteral (MkToken FALSE _ _) = True
isBooleanLiteral _ = False

isNilLiteral     : Token -> Bool
isNilLiteral (MkToken NILV _ _) = True
isNilLiteral _ = False

isStringLiteral : Token -> Bool
isStringLiteral (MkToken (STRING  _) _ _) = True
isStringLiteral _ = False

isIdentifier : Token -> Bool
isIdentifier (MkToken (IDENTIFIER _) _ _) = True
isIdentifier _ = False

parseToken : ( Token -> Bool ) -> Parser (List Token) Token
parseToken predicate =
  do
    tokens <- lift get
    case tokens of
      [] => left [ "No token found" ]
      (x::xs) => if predicate x
        then do
          lift . put $ xs
          pure x
          -- pure . trace ("parseToken-right: tokens'" ++ show x ++ "::" ++ show xs ++ "'") $ x
        -- else left [ "parseToken: token '" ++ (show x) ++ "' does not fulfill predicate" ]
        else left [ "parseToken: token '" ++ (show x) ++ "' in '" ++ show tokens ++ "' does not fulfill predicate" ]

parseLineEnd : Parser (List Token) ()
parseLineEnd =
  do
    _ <- (
      parseToken (tokenTypeIs NEWLINE)
      <|>
      parseToken (tokenTypeIs SEMICOLON)
      )
    pure ()

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

-- readInteger : String -> Maybe Integer
-- readInteger str =
--   let
--     lsCh = unpack str
--     mapped = sequence $ (digitToInt) <$> lsCh
--     packInteger : Integer -> List Int -> Integer
--     packInteger int [] = int
--     packInteger int (x::xs) = packInteger ( int * 10 + (cast x) ) xs
--   in
--     case mapped of
--       Nothing => Nothing
--       Just lsInt => Just (packInteger 0 lsInt)

readInteger : String -> Maybe Integer
readInteger str =
  let
    lsCh = unpack str

    (sign, digits) =
      case lsCh of
        ('-' :: xs) => (-1, xs)
        ('+' :: xs) => (1, xs)
        xs           => (1, xs)

    mapped = sequence $ (digitToInt) <$> digits

    packInteger : Integer -> List Int -> Integer
    packInteger acc [] = acc
    packInteger acc (x :: xs) =
      packInteger (acc * 10 + cast x) xs

  in
    case mapped of
      Nothing => Nothing
      Just lsInt =>
        Just (cast sign * packInteger 0 lsInt)
