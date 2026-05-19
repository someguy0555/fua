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

record Env where
  constructor MkEnv
  parent : Maybe Env
  nextId : RefId
  vars   : SortedMap Identifier Sym

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
  RLet    : RefId -> ExprType -> Maybe ResolvedExpr -> ResolvedStmt

  RFunc   : RefId -> List RefId -> ResolvedStmt -> ResolvedStmt

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

  show (RFunc fid params body) =
    "RFunc(fid=" ++ show fid ++
    ", params=" ++ show params ++
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
  case val of
    Nothing =>
      Right (env1, RLet id ty Nothing)

    Just v =>
      do
        rv <- resolveExpr env1 v
        Right (env1, RLet id ty (Just rv))


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
      (fnEnv2, paramIds) = bindParams fnEnv params
  in
    do
      (fnEnvFinal, rb) <- resolveStmt fnEnv2 body
      Right (env1, RFunc fid paramIds rb)

------------------------------------------------------------
-- TYPE INFERENCE
------------------------------------------------------------

data Constraint
  = CEq ExprType ExprType
  | CRef RefId ExprType

covering
Show Constraint where
  show (CEq  a b) = show a ++ " == " ++ show b
  show (CRef r a) = "RefId " ++ show r ++ " " ++ show a

lookupSymById : RefId -> Env -> Maybe Sym
lookupSymById target env =
  let direct =
        findMatch (SortedMap.toList env.vars)
  in case direct of
       Just s  => Just s
       Nothing =>
         case env.parent of
           Just p  => lookupSymById target p
           Nothing => Nothing
  where
    findMatch : List (Identifier, Sym) -> Maybe Sym
    findMatch [] = Nothing
    findMatch ((_, SymVar ty id) :: xs) =
      if id == target then Just (SymVar ty id)
      else findMatch xs

    findMatch ((_, SymFunc args ret id) :: xs) =
      if id == target then Just (SymFunc args ret id)
      else findMatch xs


lookupFuncById : RefId -> Env -> Maybe (List ExprType, ExprType)
lookupFuncById fid env =
  case lookupSymById fid env of
    Just (SymFunc args ret _) => Just (args, ret)
    _ => Nothing


collectExpr : Env -> ResolvedExpr -> List Constraint -> (ExprType, List Constraint)
collectList : Env -> List ResolvedExpr -> List Constraint -> (List ExprType, List Constraint)
collectStmt : Env -> ResolvedStmt -> List Constraint -> List Constraint
collectStmtList : Env -> List ResolvedStmt -> List Constraint -> List Constraint
solve : List Constraint -> Either ErrorMsg ()

collectExpr env (RConst ty _) cs =
  (ty, cs)

collectExpr env (RVar ty id) cs =
  (ty, CRef id ty :: cs)

collectExpr env (ROp _ op args) cs =
  let (argTs, cs1) = collectList env ( toList args ) cs in
  case op of
    Add =>
      case argTs of
        (t1 :: _) =>
          (TypeInt, CEq t1 TypeInt :: cs1)
        _ =>
          (TypeInt, cs1)

    Sub =>
      (TypeInt, cs1)

    Mul =>
      (TypeInt, cs1)

    Div =>
      (TypeInt, cs1)

    Equal =>
      (TypeBool, cs1)

    Less =>
      (TypeBool, cs1)

    _ =>
      (TypeUnknown, cs1)

collectExpr env (RCall _ fid args) cs =
  case lookupFuncById fid env of
    Just (argTypes, retType) =>
      let (argTs, cs1) = collectList env args cs in

      -- constrain each argument against expected parameter type
      let cs2 =
            zipWith (\expected, actual =>
              CEq expected actual
            ) argTypes argTs ++ cs1

      in (retType, cs2)

    Nothing =>
      let (_, cs1) = collectList env args cs in
      (TypeUnknown, cs1)

collectList env [] cs =
  ([], cs)

collectList env (x :: xs) cs =
  let (t, cs1)   = collectExpr env x cs
      (ts, cs2)  = collectList env xs cs1
  in (t :: ts, cs2)


collectStmt env (RExpr e) cs =
  snd (collectExpr env e cs)

collectStmt env (RLet id TypeUnknown Nothing) cs = cs
collectStmt env (RLet id ty Nothing) cs = CRef id ty :: cs

collectStmt env (RLet id ty (Just e)) cs =
  let (t, cs1) = collectExpr env e cs
  in
    case ty of
      TypeUnknown => CRef id ty :: cs1
      _           => CEq ty t :: CRef id ty :: cs1

collectStmt env (RAssign id e) cs =
  let (t, cs1) = collectExpr env e cs
  in CRef id t :: cs1

collectStmt env (RBlock _ ss) cs =
  collectStmtList env ss cs

collectStmt env (RIf c b) cs =
  let (_, cs1) = collectExpr env c cs
  in collectStmt env b cs1

collectStmt env (RWhile c b) cs =
  let (_, cs1) = collectExpr env c cs
  in collectStmt env b cs1

collectStmt env (RReturn Nothing) cs =
  cs

collectStmt env (RReturn (Just e)) cs =
  snd (collectExpr env e cs)

collectStmt env RBreak cs =
  cs

collectStmt env (RFunc fid params body) cs =
  collectStmt env body cs

collectStmtList env [] cs =
  cs

collectStmtList env (s :: ss) cs =
  let cs1 = collectStmt env s cs
  in collectStmtList env ss cs1

solve [] =
  Right ()

solve (CEq a b :: cs) =
  if a == b then
    solve cs
  else
    Left ["Type mismatch: " ++ show a ++ " vs " ++ show b ++ show "; " ++ show cs]

solve (CRef _ _ :: cs) =
  solve cs
