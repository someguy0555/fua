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
import Expr
import Stmt
import Utility

data SymType : Type where
  Var   : Integer -> SymType
  Label : SymType

Show SymType where
  show (Var integer) = "Var " ++ show integer
  show (Label) = "Label"

-- Runtime environment as well
public export
record Env where
  constructor MkEnv
  symbols : SortedMap Identifier SymType
  code    : List Stmt

covering
Show Env where
  show (MkEnv symbols code) = "symbols: " ++ show ( Data.SortedMap.toList symbols ) ++ "; code: " ++ show code ++ ";"

data CheckError = IsError String Identifier
  -- = VarLabelConflict Identifier
  -- | LabelVarConflict Identifier
  -- | GotoToVar Identifier
  -- | MissingLabel Identifier
  --
Show CheckError where
  show (IsError str identifier) = str ++ ": " ++ show identifier

lookupSym : Identifier -> SortedMap Identifier SymType -> Maybe SymType
lookupSym = SortedMap.lookup

pass1 : List Stmt -> Env -> Either CheckError Env

pass1 [] env = Right env

pass1 (StmtLabel name :: xs) env =
  case lookupSym name env.symbols of
    Just Label => Left (IsError "IsDuplicatelabel" name)
    Just (Var _) => Left (IsError "LabelVarConflict" name)
    Nothing =>
      let symbols' = insert name Label env.symbols
      in pass1 xs (MkEnv symbols' env.code)

pass1 (StmtAssign name _ :: xs) env =
  case lookupSym name env.symbols of
    Just Label =>
      Left (IsError "LabelVarConflict" name)
    Just (Var _) =>
      pass1 xs env
    Nothing =>
      let symbols' = insert name (Var 0) env.symbols
      in pass1 xs (MkEnv symbols' env.code)

pass1 (StmtPrint _ :: xs) env =
  pass1 xs env

pass1 (StmtIf _ _ :: xs) env =
  pass1 xs env

pass1 (StmtGoto _ :: xs) env =
  pass1 xs env

pass2 : List Stmt -> SortedMap Identifier SymType -> Either CheckError ()

pass2 [] _ = Right ()

pass2 (StmtLabel _ :: xs) env =
  pass2 xs env

pass2 (StmtAssign _ _ :: xs) env =
  pass2 xs env

pass2 (StmtPrint _ :: xs) env =
  pass2 xs env

pass2 (StmtIf _ name :: xs) env =
  case lookupSym name env of
    Nothing =>
      Left (IsError "MissingLabel" name)

    Just (Var _) =>
      Left (IsError "GotoToVar" name)

    Just Label =>
      pass2 xs env

pass2 (StmtGoto name :: xs) env =
  case lookupSym name env of
    Nothing =>
      Left (IsError "MissingLabel" name)

    Just (Var _) =>
      Left (IsError "GotoToVar" name)

    Just Label =>
      pass2 xs env

checkProgram : List Stmt -> Either CheckError Env
checkProgram stmts =
  let initEnv = MkEnv empty empty
  in case pass1 stmts initEnv of
       Left err => Left err
       Right env =>
         case pass2 stmts env.symbols of
           Left err => trace ( "checkProgram: " ++ show stmts ) $ Left err
           Right _  => Right (MkEnv env.symbols stmts)
