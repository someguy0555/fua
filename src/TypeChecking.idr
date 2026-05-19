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

typeCheckExpr : Env -> ResolvedExpr -> Either ErrorMsg ExprType
typeCheckStmt : Env -> ExprType -> ResolvedStmt -> Either ErrorMsg ()

typeCheckExpr env (RConst ty _) =
  Right ty

typeCheckExpr env (RVar ty id) =
  Right ty

typeCheckExpr env (ROp _ op args) =
  do
    argTypes <- traverse (typeCheckExpr env) (toList args)

    case op of
      Add =>
        case argTypes of
          [TypeInt, TypeInt] =>
            Right TypeInt

          _ =>
            Left ["Operator '+' expects Int Int"]

      Sub =>
        case argTypes of
          [TypeInt, TypeInt] =>
            Right TypeInt

          _ =>
            Left ["Operator '-' expects Int Int"]

      Mul =>
        case argTypes of
          [TypeInt, TypeInt] =>
            Right TypeInt

          _ =>
            Left ["Operator '*' expects Int Int"]

      Div =>
        case argTypes of
          [TypeInt, TypeInt] =>
            Right TypeInt

          _ =>
            Left ["Operator '/' expects Int Int"]

      Equal =>
        case argTypes of
          [a, b] =>
            if a == b then
              Right TypeBool
            else
              Left ["Equality arguments must match"]

          _ =>
            Left ["Invalid equality expression"]

      Less =>
        case argTypes of
          [TypeInt, TypeInt] =>
            Right TypeBool

          _ =>
            Left ["Operator '<' expects Int Int"]

      _ =>
        Left ["Unsupported operator"]


typeCheckExpr env (RCall retTy fid args) =
  case lookupSymById fid env of
    Just (SymFunc paramTypes fnRetTy _) =>
      do
        argTypes <- traverse (typeCheckExpr env) args

        if length argTypes /= length paramTypes
          then Left ["Incorrect number of function arguments"]
          else do
              traverse_
                (\(actual, expected) =>
                  if actual == expected
                    then Right ()
                    else Left
                      [ "Function argument mismatch: expected "
                      ++ show expected
                      ++ ", got "
                      ++ show actual
                      ]
                )
                (zip argTypes paramTypes)

              if retTy == fnRetTy
                then Right retTy
                else Left ["Resolved call return type mismatch"]

    _ => Left ["Invalid function reference"]

typeCheckStmt env retTy (RExpr e) =
  do
    _ <- typeCheckExpr env e
    Right ()

typeCheckStmt env retTy (RLet _ declaredTy expr) =
  do
    exprTy <- typeCheckExpr env expr

    if declaredTy == exprTy
      then Right ()
      else Left
        [ "Let type mismatch: expected "
        ++ show declaredTy
        ++ ", got "
        ++ show exprTy
        ]

typeCheckStmt env retTy (RAssign id expr) =
  case lookupSymById id env of
    Just (SymVar varTy _) =>
      do
        exprTy <- typeCheckExpr env expr

        if varTy == exprTy
          then Right ()
          else Left
            [ "Assignment type mismatch: expected "
            ++ show varTy
            ++ ", got "
            ++ show exprTy
            ]

    _ =>
      Left ["Assignment to invalid variable"]

typeCheckStmt env retTy (RIf cond body) =
  do
    condTy <- typeCheckExpr env cond

    if condTy /= TypeBool
      then Left ["If condition must be Bool"]
      else typeCheckStmt env retTy body

typeCheckStmt env retTy (RWhile cond body) =
  do
    condTy <- typeCheckExpr env cond

    if condTy /= TypeBool
      then Left ["While condition must be Bool"]
      else typeCheckStmt env retTy body

typeCheckStmt env retTy (RReturn Nothing) =
  if retTy == TypeNil then
    Right ()
  else
    Left ["Non-nil function must return a value"]

typeCheckStmt env retTy (RReturn (Just expr)) =
  do
    exprTy <- typeCheckExpr env expr

    if exprTy == retTy
      then Right ()
      else Left
        [ "Return type mismatch: expected "
        ++ show retTy
        ++ ", got "
        ++ show exprTy
        ]

typeCheckStmt env retTy (RBlock _ stmts) =
  traverse_ (typeCheckStmt env retTy) stmts

typeCheckStmt env retTy (RFunc _ _ body) =
  typeCheckStmt env retTy body

typeCheckStmt env retTy RBreak =
  Right ()
