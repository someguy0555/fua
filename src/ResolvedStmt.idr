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

import Lexer
import Parser
import Expr
import Stmt


-- record ScannerState where
--   constructor MkScannerState
--   line : Nat
--   column : Nat
--   lines : Cursor (List String) -- lines above the current one, lines below the current one.
--   currLine : Cursor String     -- left of the cursor, right of the cursor
--   tokens : List Token


-- FormatType : Format -> Type
-- FormatType (Number x) = Int -> FormatType x
-- FormatType (Str x) = String -> FormatType x
-- FormatType (Lit _ x) = FormatType x
-- FormatType End = String
--
-- toFormat : List Char -> Format
-- toFormat [] = End
-- toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
-- toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
-- toFormat (x :: xs) = Lit x (toFormat xs)
--
-- format : (fmt : Format) -> String -> FormatType fmt
-- format (Number x) acc = \i => format x (acc ++ show i)
-- format (Str x) acc = \str => format x (acc ++ str)
-- format (Lit c x) acc = format x (acc ++ (pack [c]))
-- format End str = str

-- TypedVar : ExprType -> Type
-- TypedVar TypeUnknown     = ()
-- TypedVar TypeNil         = ()
-- TypedVar TypeBool        = Bool
-- TypedVar TypeInt         = Int
-- TypedVar TypeReal        = RealNumber
-- TypedVar TypeString      = String
-- TypedVar (TypeFunc xs x) = ?TypedVar_rhs_6 -- Idk how to do this
-- TypedVar _ = ()

RefId : Type
RefId = Nat

{-
  x -> {}
-}
