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
import Resolved
import TypeChecking

data Value
  = VInt Int
  | VBool Bool
  | VReal Double
  | VString String
  | VUnit

record RTEnv where
  constructor MkRTEnv
  parent : Maybe RTEnv
  vars   : SortedMap RefId Value

lookupVal : RefId -> RTEnv -> Maybe Value
lookupVal id env =
  case SortedMap.lookup id env.vars of
    Just v  => Just v
    Nothing =>
      case env.parent of
        Just p  => lookupVal id p
        Nothing => Nothing

insertVal : RefId -> Value -> RTEnv -> RTEnv
insertVal id v env =
  { vars := SortedMap.insert id v env.vars } env

updateVal : RefId -> Value -> RTEnv -> RTEnv
updateVal id v env =
  case SortedMap.lookup id env.vars of
    Just _ =>
      { vars := SortedMap.insert id v env.vars } env
    Nothing =>
      case env.parent of
        Just p =>
          let p' = updateVal id v p
          in { parent := Just p' } env
        Nothing =>
          { vars := SortedMap.insert id v env.vars } env

record FunctionDef where
  constructor MkFn
  params : List RefId
  body   : ResolvedStmt

FunctionTable : Type
FunctionTable = SortedMap RefId FunctionDef

lookupFn : RefId -> FunctionTable -> Maybe FunctionDef
lookupFn = SortedMap.lookup

data ExecResult
  = Normal RTEnv
  | Return Value RTEnv

mergeEnv : RTEnv -> RTEnv -> RTEnv
mergeEnv (MkRTEnv p1 v1) (MkRTEnv _ v2) =
  MkRTEnv p1 (v2)
-- mergeEnv : RTEnv -> RTEnv -> RTEnv
-- mergeEnv (MkRTEnv p1 v1) (MkRTEnv _ v2) =
--  MkRTEnv p1 (SortedMap.union v2 v1)

evalExpr : RTEnv -> FunctionTable -> ResolvedExpr -> Value

evalExpr env ft (RConst ty v) =
  case ty of
    TypeInt    => VInt (cast v)
    TypeBool   => VBool (cast v)
    TypeReal   => VReal (cast v)
    TypeString => VString (cast v)
    _          => VUnit

evalExpr env ft (RVar _ id) =
  case lookupVal id env of
    Just v  => v
    Nothing => VUnit

evalExpr env ft (ROp _ op args) =
  case (op, args) of
    (Add, [a, b]) =>
      let VInt x = evalExpr env ft a
          VInt y = evalExpr env ft b
      in VInt (x + y)

    (Sub, [a, b]) =>
      let VInt x = evalExpr env ft a
          VInt y = evalExpr env ft b
      in VInt (x - y)

    (Mul, [a, b]) =>
      let VInt x = evalExpr env ft a
          VInt y = evalExpr env ft b
      in VInt (x * y)

    (Div, [a, b]) =>
      let VInt x = evalExpr env ft a
          VInt y = evalExpr env ft b
      in VInt (x `div` y)

    (Equal, [a, b]) =>
      let v1 = evalExpr env ft a
          v2 = evalExpr env ft b
      in VBool (v1 == v2)

    (Less, [a, b]) =>
      let VInt x = evalExpr env ft a
          VInt y = evalExpr env ft b
      in VBool (x < y)

    _ =>
      VUnit

evalExpr env ft (RCall _ fid args) =
  case lookupFn fid ft of
    Nothing => VUnit

    Just (MkFn params body) =>
      let argVals = map (evalExpr env ft) args

          fnEnv =
            MkRTEnv (Just env)
              (foldl (\e, (pid, v) => insertVal pid v e)
                     emptyEnv
                     (zip params argVals))

      in case execStmt fnEnv ft body of
           Normal _       => VUnit
           Return v _     => v

execStmt : RTEnv -> FunctionTable -> ResolvedStmt -> ExecResult
execStmtList : RTEnv -> FunctionTable -> List ResolvedStmt -> ExecResult

execStmt env ft (RExpr e) =
  Normal env

execStmt env ft (RLet id _ expr) =
  let v = evalExpr env ft expr
  in Normal (insertVal id v env)

execStmt env ft (RAssign id expr) =
  let v = evalExpr env ft expr
  in Normal (updateVal id v env)

execStmt env ft (RBlock _ stmts) =
  execStmtList env ft stmts

execStmt env ft (RIf cond body) =
  case evalExpr env ft cond of
    VBool True  => execStmt env ft body
    VBool False => Normal env
    _           => Normal env

execStmt env ft (RWhile cond body) =
  let loop : RTEnv -> ExecResult
      loop env' =
        case evalExpr env' ft cond of
          VBool True =>
            case execStmt env' ft body of
              Normal env'' => loop env''
              Return v e   => Return v e
          _ => Normal env'
  in loop env

execStmt env ft (RReturn Nothing) =
  Return VUnit env

execStmt env ft (RReturn (Just e)) =
  Return (evalExpr env ft e) env

execStmt env ft RBreak =
  Normal env

execStmt env ft (RFunc _ _ _ _) =
  Normal env

execStmtList env ft [] = Normal env

execStmtList env ft (s :: ss) =
  case execStmt env ft s of
    Normal env' =>
      execStmtList env' ft ss

    r@(Return _ _) =>
      r
