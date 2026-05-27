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

import Expr
import Stmt
import Utility
import Resolve
import Interpreter

-- lengthsAreEqual1 : { k : Nat } -> { x : a } -> { xs : Vect n a } -> ( length xs = k ) -> (length (x :: xs) = S k)
-- lengthsAreEqual2 : { k : Nat } -> { x : a } -> { xs : Vect n a } -> (length (x :: xs) = S k) -> ( length xs = k)
--
-- arityCorrect : { n : Nat } -> (op : Operator n) -> (args : Vect n Expr) -> length args = n
-- arityCorrect {n = 0} _ [] = Refl
-- arityCorrect {n = (S k)} op (x::xs) = cong (S) (arityCorrect ?op xs) --cong (S) (arityCorrect op xs)
arityCorrect : { n : Nat } -> (op : Operator n) -> (args : Vect n Expr) -> length args = n
arityCorrect {n = 0} _ [] = Refl
arityCorrect {n = (S k)} op (x::xs) = cong (S) (arityCorrect ?op xs) --cong (S) (arityCorrect op xs)

-- arityCorrect {n = 1} _ (x :: []) = Refl
-- arityCorrect {n = 2} _ (x :: (y :: [])) = Refl

StmtIsJump : Stmt -> Type
StmtIsJump (StmtGoto _)   = Unit
StmtIsJump (StmtIf _ _)   = Unit
StmtIsJump _              = Void

TargetExists : SortedMap Identifier SymType -> Stmt -> Type

TargetExists env (StmtGoto name) =
  lookupSym name env = Just Label

TargetExists env (StmtIf _ name) =
  lookupSym name env = Just Label

TargetExists env _ =
  Unit

StmtSound : SortedMap Identifier SymType -> Stmt -> Type
StmtSound env stmt =
  StmtIsJump stmt -> TargetExists env stmt

ProgramValid : SortedMap Identifier SymType -> List Stmt -> Type
ProgramValid env [] = Unit
ProgramValid env (x :: xs) =
  (StmtSound env x, ProgramValid env xs)

-- stmtSoundGoto :
--   lookupSym name env = Just Label ->
--   StmtSound env (StmtGoto name)
--
-- stmtSoundGoto prf _ = prf
--
-- stmtSoundIf :
--   lookupSym name env = Just Label ->
--   StmtSound env (StmtIf _ name)
--
-- stmtSoundIf prf _ = prf

checkProgramSound :
  (env : SortedMap Identifier SymType) ->
  (stmts : List Stmt) ->
  Either CheckError (ProgramValid env stmts)
checkProgramSound env [] = Right ()
checkProgramSound env (x :: xs) = ?checkProgramSound_rhs_1

LabelsOf : List Stmt -> List Identifier
LabelsOf [] = []
LabelsOf (StmtLabel l :: xs) = l :: LabelsOf xs
LabelsOf (_ :: xs) = LabelsOf xs

-- LabelExists : Identifier -> List Stmt -> Type
-- LabelExists l stmts =
--   Elem l (LabelsOf stmts)

-- Deterministic :
--   (s : EvalState) ->
--   (s1, s2 : EvalState) ->
--   step s = s1 ->
--   step s = s2 ->
--   s1 = s2
--
-- Deterministic s s1 s2 prf1 prf2 =
--   case s of
--
--     Done env v =>
--       rewrite prf1 in prf2
--
--     Running env (ExprOperand n) stack =>
--       -- only one clause exists → same result
--       Refl
--
--     Running env (ExprVariable x) stack =>
--       case lookup x env.symbols of
--         Just v  => Refl
--         Nothing => Refl
--
--     Running env (ExprOperator op args) stack =>
--       case op of
--         Add => Refl
--         Sub => Refl
--         Mul => Refl
--         Div => Refl
--         Mod => Refl
--         Greater => Refl
--         Less => Refl
--         Equal => Refl
--         NotEqual => Refl
--         And => Refl
--         Or => Refl
--         Neg => Refl
--         Not => Refl
--
-- -- Progress :
-- --   (s : EvalState) ->
-- --   Not (isDone s) ->
-- --   Not (step s = s)
-- --
-- -- isDone : EvalState -> Bool
-- -- isDone (Done _ _) = True
-- -- isDone _          = False

-- theorem_eval_correct :
--   (env : Env) ->
--   (e : Expr) ->
--   runExpr env e = eval env e
-- theorem_eval_correct env (ExprOperand n) = Refl
-- theorem_eval_correct env (ExprVariable x) = Refl
-- theorem_eval_correct env (ExprOperator op args) =
--   case op of
--
--     Add =>
--       case args of
--         [a, b] =>
--           let ih1 = theorem_eval_correct env a
--               ih2 = theorem_eval_correct env b
--           in rewrite ih1 in rewrite ih2 in Refl
--
--     Sub =>
--       case args of
--         [a, b] =>
--           let ih1 = theorem_eval_correct env a
--               ih2 = theorem_eval_correct env b
--           in rewrite ih1 in rewrite ih2 in Refl
--
--     Mul =>
--       case args of
--         [a, b] =>
--           let ih1 = theorem_eval_correct env a
--               ih2 = theorem_eval_correct env b
--           in rewrite ih1 in rewrite ih2 in Refl
--
--     Div =>
--       case args of
--         [a, b] =>
--           let ih1 = theorem_eval_correct env a
--               ih2 = theorem_eval_correct env b
--           in rewrite ih1 in rewrite ih2 in Refl
--
--     Mod =>
--       case args of
--         [a, b] =>
--           let ih1 = theorem_eval_correct env a
--               ih2 = theorem_eval_correct env b
--           in rewrite ih1 in rewrite ih2 in Refl
--
--     _ => Refl

theorem_eval_operand :
  (env : Env) ->
  (n : Integer) ->
  runExpr env (ExprOperand n) = n
theorem_eval_operand env n = Refl

theorem_eval_variable :
  (env : Env) ->
  (x : Identifier) ->
  eval env (ExprVariable x) = getVar x env
theorem_eval_variable env x = Refl

exprSize : Expr -> Nat
exprSize (ExprOperand _) = 1
exprSize (ExprVariable _) = 1
exprSize (ExprOperator _ args) = 1 + sum (map exprSize (toList args))

theorem_exprSize_positive :
  (e : Expr) -> exprSize e = 0 -> Void
theorem_exprSize_positive (ExprOperand _) prf impossible
theorem_exprSize_positive (ExprVariable _) prf impossible
theorem_exprSize_positive (ExprOperator _ _) prf impossible

theorem_duplicate_label_rejected :
  (name : Identifier) ->
  (xs : List Stmt) ->
  (env : Env) ->
  lookupSym name env.symbols = Just Label ->
  pass1 (StmtLabel name :: xs) env =
    Left (IsError "IsDuplicatelabel" name)

theorem_duplicate_label_rejected _ _ _ prf = rewrite prf in Refl
