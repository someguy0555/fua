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

RefId : Type
RefId = Nat

data Sym
  = SymVar ExprType RefId
  | SymFunc (List ExprType) ExprType RefId

public export
record Env where
  constructor MkEnv
  parent : Maybe Env
  nextId : RefId
  vars   : SortedMap Identifier Sym

emptyEnv : Env
emptyEnv = MkEnv Nothing 1 empty

data ResolvedExpr : Type where
  RConst : Show a => ExprType -> a -> ResolvedExpr
  RVar   : ExprType -> RefId -> ResolvedExpr
  ROp    : ExprType -> Operator n -> Vect n ResolvedExpr -> ResolvedExpr
  RCall  : ExprType -> RefId -> List ResolvedExpr -> ResolvedExpr

data ResolvedStmt : Type where
  RBlock  : Env -> List ResolvedStmt -> ResolvedStmt
  RExpr   : ResolvedExpr -> ResolvedStmt

  RIf     : ResolvedExpr -> ResolvedStmt -> ResolvedStmt
  RWhile  : ResolvedExpr -> ResolvedStmt -> ResolvedStmt

  RReturn : Maybe ResolvedExpr -> ResolvedStmt
  RBreak  : ResolvedStmt

  RAssign : RefId -> ResolvedExpr -> ResolvedStmt
  RLet    : RefId -> ExprType -> ResolvedExpr -> ResolvedStmt

  RFunc : RefId -> List (RefId, ExprType) -> ExprType -> ResolvedStmt -> ResolvedStmt
  -- RFunc   : RefId -> List RefId -> ResolvedStmt -> ResolvedStmt

------------------------------------------------------------
-- SHOW: RESOLVED EXPR
------------------------------------------------------------

covering
Show ResolvedExpr where
  show (RConst ty v) =
    "RConst(" ++ show v ++ " : " ++ show ty ++ ")"

  show (RVar ty id) =
    "RVar(" ++ show id ++ " : " ++ show ty ++ ")"

  show (ROp ty op args) =
    "ROp(" ++ show op ++ ", " ++ show args ++ " : " ++ show ty ++ ")"

  show (RCall ty fid args) =
    "RCall(fid=" ++ show fid ++ ", args=" ++ show args ++ ", ret=" ++ show ty ++ ")"


------------------------------------------------------------
-- SHOW: RESOLVED STMT
------------------------------------------------------------

covering
Show ResolvedStmt where
  show (RBlock _ stmts) =
    "RBlock(" ++ show stmts ++ ")"

  show (RExpr e) =
    "RExpr(" ++ show e ++ ")"

  show (RIf c b) =
    "RIf(" ++ show c ++ ", " ++ show b ++ ")"

  show (RWhile c b) =
    "RWhile(" ++ show c ++ ", " ++ show b ++ ")"

  show (RReturn Nothing) =
    "RReturn()"

  show (RReturn (Just e)) =
    "RReturn(" ++ show e ++ ")"

  show RBreak =
    "RBreak"

  show (RAssign id e) =
    "RAssign(" ++ show id ++ ", " ++ show e ++ ")"

  show (RLet id ty val) =
    "RLet(" ++ show id ++ " : " ++ show ty ++ ", " ++ show val ++ ")"

  show (RFunc fid params retType body) =
    "RFunc(fid=" ++ show fid ++
    ", params=" ++ show params ++
    ", retType=" ++ show retType ++
    ", body=" ++ show body ++ ")"


------------------------------------------------------------
-- SHOW: SYMBOL
------------------------------------------------------------

covering
Show Sym where
  show (SymVar ty id) =
    "SymVar(" ++ show id ++ " : " ++ show ty ++ ")"

  show (SymFunc args ret id) =
    "SymFunc(fid=" ++ show id ++
    ", args=" ++ show args ++
    ", ret=" ++ show ret ++ ")"


------------------------------------------------------------
-- SHOW: ENV
------------------------------------------------------------

covering
Show Env where
  show (MkEnv parent next vars) =
    "Env(nextId=" ++ show next ++
    ", vars=" ++ show (SortedMap.toList vars) ++
    ", parent=" ++ show (map (const "<parent>") parent) ++ ")"
-- Show Env where
--   show (MkEnv parent next vars) =
--     "Env(nextId=" ++ show next ++
--     ", vars=" ++ show vars ++
--     ", parent=" ++ show parent ++ ")"

------------------------------------------------------------
-- LOOKUP
------------------------------------------------------------

lookupSym : Identifier -> Env -> Either ErrorMsg Sym
lookupSym "print" env = Right (SymFunc [TypeString] TypeNil 0)
lookupSym name env =
  case SortedMap.lookup name env.vars of
    Just sym => Right sym
    Nothing =>
      case env.parent of
        Just p  => lookupSym name p
        Nothing => Left ["Undefined identifier: " ++ name]


------------------------------------------------------------
-- INSERT VARIABLE
------------------------------------------------------------

insertVar : Identifier -> ExprType -> Env -> (Env, RefId)
insertVar name ty env =
  let id = env.nextId
      sym = SymVar ty id
      vars' = SortedMap.insert name sym env.vars
      env' = { nextId := id + 1, vars := vars' } env
  in (env', id)


------------------------------------------------------------
-- INSERT FUNCTION
------------------------------------------------------------

insertFunc : Identifier -> List ExprType -> ExprType -> Env -> (Env, RefId)
insertFunc name argTypes retType env =
  let id = env.nextId
      sym = SymFunc argTypes retType id
      vars' = SortedMap.insert name sym env.vars
      env' = { nextId := id + 1, vars := vars' } env
  in (env', id)

------------------------------------------------------------
-- PARAM BINDING
------------------------------------------------------------

bindParams : Env -> List IdentifierAndType -> (Env, List RefId)
bindParams env [] = (env, [])
bindParams env ((n, ty) :: xs) =
  let (env1, id) = insertVar n ty env
      (env2, ids) = bindParams env1 xs
  in (env2, id :: ids)


------------------------------------------------------------
-- EXPRESSION RESOLUTION
------------------------------------------------------------

resolveExpr : Env -> Expr -> Either ErrorMsg ResolvedExpr

resolveExpr env (ExprOperand ty v) =
  Right (RConst ty v)

resolveExpr env (ExprVariable ty name) =
  case lookupSym name env of
    Right (SymVar ty' id) => Right (RVar ty' id)
    _ => Left ["Not a variable: " ++ name]

resolveExpr env (ExprOperator ty op exprs) =
  do
    args <- traverse (resolveExpr env) exprs
    Right (ROp ty op args)

resolveExpr env (ExprCall fn args) =
  case fn of
    ExprVariable _ name =>
      case lookupSym name env of
        Right (SymFunc _ retTy id) =>
          do
            args' <- traverse (resolveExpr env) args
            Right (RCall retTy id args')
        _ =>
          Left ["Not a function: " ++ name]

    _ =>
      Left ["Only direct function calls supported"]


------------------------------------------------------------
-- STATEMENT RESOLUTION
------------------------------------------------------------

resolveStmtList : Env -> List Stmt -> Either ErrorMsg (Env, List ResolvedStmt)
resolveStmt : Env -> Stmt -> Either ErrorMsg (Env, ResolvedStmt)

resolveStmtList env [] = Right (env, [])

resolveStmtList env (s :: ss) =
  do
    (env1, r1) <- resolveStmt env s
    (env2, rs)  <- resolveStmtList env1 ss
    Right (env2, r1 :: rs)

resolveStmt env (StmtLet (name, ty) val) =
  let (env1, id) = insertVar name ty env in
    do
      rv <- resolveExpr env1 val
      Right (env1, RLet id ty rv)


resolveStmt env (StmtAssign name expr) =
  case lookupSym name env of
    Right (SymVar _ id) =>
      do
        e <- resolveExpr env expr
        Right (env, RAssign id e)

    _ =>
      Left ["Assignment to unknown variable"]


resolveStmt env (StmtBlock stmts) =
  let child = MkEnv (Just env) env.nextId empty in
  do
    (child', rs) <- resolveStmtList child stmts
    Right (env, RBlock child' rs)


resolveStmt env (StmtExpr e) =
  do
    e' <- resolveExpr env e
    Right (env, RExpr e')


resolveStmt env (StmtIf cond body) =
  do
    c <- resolveExpr env cond
    (env1, b) <- resolveStmt env body
    Right (env1, RIf c b)


resolveStmt env (StmtWhile cond body) =
  do
    c <- resolveExpr env cond
    (env1, b) <- resolveStmt env body
    Right (env1, RWhile c b)


resolveStmt env (StmtReturn Nothing) =
  Right (env, RReturn Nothing)

resolveStmt env (StmtReturn (Just e)) =
  do
    e' <- resolveExpr env e
    Right (env, RReturn (Just e'))


resolveStmt env StmtBreak =
  Right (env, RBreak)

resolveStmt env (StmtFunc (name, retTy) params body) =
  let paramTypes = map snd params
      (env1, fid) = insertFunc name paramTypes retTy env

      fnEnv = MkEnv (Just env1) env1.nextId empty

      -- bindParams already gives RefIds in order
      (fnEnv2, paramIds) = bindParams fnEnv params

      paramIdTypes = zip paramIds paramTypes
  in
    do
      (fnEnvFinal, rb) <- resolveStmt fnEnv2 body
      Right (env1, RFunc fid paramIdTypes retTy rb)

-- resolveStmt env (StmtFunc (name, retTy) params body) =
--   let paramTypes = map snd params
--       (env1, fid) = insertFunc name paramTypes retTy env
--       fnEnv = MkEnv (Just env1) env1.nextId empty
--       (fnEnv2, paramIds) = bindParams fnEnv params
--   in
--     do
--       (fnEnvFinal, rb) <- resolveStmt fnEnv2 body
--       Right (env1, RFunc fid paramIds rb)
