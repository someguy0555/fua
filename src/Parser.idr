module Main

import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Debug.Trace
import System.File

record ParserState where
  constructor MkParserState
  input  : String
  line   : Nat
  column : Nat

ErrorMsg = String
Parser a = EitherT ErrorMsg (State ParserState) a

parse : Parser a -> ParserState -> (ParserState, Either ErrorMsg a)
parse p state = runState state (runEitherT p)

parseText : Parser a -> String -> (ParserState, Either ErrorMsg a)
parseText p str = runState (MkParserState str 0 0) (runEitherT p)

-- Runs the parser 0 or more times.
-- Only ever returns 'Right'
many : Parser a -> Parser ( List a )
many parser =
  do
    state <- lift get
    case parse parser state of
      (_, Left _) => right []
      (rest, Right val) =>
        case (parse $ many parser) rest of
          (_, Left _) => do
            lift . put $ rest
            right [val]
          (rest', Right valLs) => do
            lift . put $ rest'
            right $ val::valLs

-- Runs the parser 1 or more times.
-- Returns 'Left' on failure.
some : Parser a -> Parser ( List a)
some parser =
  do
    state <- lift get
    case ( parse $ many parser ) state of
      (_, Right []) => left "Expected at least one match"
      (state', Right r) => do
        lift . put $ state'
        right r
      (state', Left e) => left e -- Doesn't happen, but put this here anyway

parserOverwriteError : (String -> String) -> Parser a -> Parser a
parserOverwriteError func parser =
  do
    state <- lift get
    case (parse parser) state of
      (_, Left err) => left . func $ err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

