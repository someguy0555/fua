module Main

import Data.List
import Data.String
import Control.Monad.State
import Data.Either
import Control.Monad.Error.Either

import Debug.Trace
import System.File

ErrorMsg = List String
Parser input return = EitherT ErrorMsg (State input) return

parse : Parser b a -> b -> (b, Either ErrorMsg a)
parse p state = runState state (runEitherT p)

-- Runs the parser 0 or more times.
-- Only ever returns 'Right'
many : Parser b a -> Parser b ( List a )
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
some : Parser b a -> Parser b ( List a )
some parser =
  do
    state <- lift get
    case ( parse $ many parser ) state of
      (_, Right []) => left ["Expected at least one match"]
      (state', Right r) => do
        lift . put $ state'
        right r
      (state', Left e) => left e -- Doesn't happen, but put this here anyway

parserOverwriteError : (ErrorMsg -> ErrorMsg) -> Parser b a -> Parser b a
parserOverwriteError func parser =
  do
    state <- lift get
    case (parse parser) state of
      (_, Left err) => left . func $ err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

parseBasic : Parser a b -> Parser a b
parseBasic parser =
  do
    state <- lift get
    case (parse parser) state of
      (_, Left err) => left err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

tryParse : a -> Parser a b -> Parser a b
tryParse resetState parser =
  do
    state <- lift get
    case (parse parser) state of
      (_, Left err) => do
        lift . put $ resetState -- attempting to restore the old state
        left err
      (state', Right rh) => do
        lift . put $ state'
        pure rh

-- orElse : Parser a b -> Parser a b -> Parser a b
-- orElse parserA parserB =
--   do
--     state <- lift get
--     case (parse parserA) state of
--          (state', Right rh) => do
--            lift . put $ state'
--            pure rh
--          (_, Left err) => left err
