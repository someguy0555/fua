module Main

import Data.List
import Data.SortedMap
import Data.Vect
import Data.String
import Control.Monad.State
import System.File
import Debug.Trace

import Expr
import Stmt
import Utility
import Resolve
import Theorem

data Value
  = VInt Integer

Eq Value where
  (==) (VInt x) (VInt y) = x == y

Show Value where
  show (VInt x) = show x

record RT where
  constructor MkRT
  env   : Env
  pc    : Nat

getVar : Identifier -> Env -> Integer
getVar x env =
  case SortedMap.lookup x env.symbols of
    Just (Var v) => v
    _            => 0

setVar : Identifier -> Integer -> Env -> Env
setVar x v env =
  let sym = insert x (Var v) env.symbols
  in { symbols := sym } env

-- eval : Env -> Expr -> Integer
-- eval env (ExprOperand n) = n
--
-- eval env (ExprVariable x) = getVar x env
--
-- eval env (ExprOperator op args) =
--   case op of
--     Add =>
--       case args of
--         [a,b] => eval env a + eval env b
--         _     => 0
--
--     Sub =>
--       case args of
--         [a,b] => eval env a - eval env b
--         _     => 0
--
--     Mul =>
--       case args of
--         [a,b] => eval env a * eval env b
--         _     => 0
--
--     Div =>
--       case args of
--         [a,b] => eval env a `div` eval env b
--         _     => 0
--
--     Mod =>
--       case args of
--         [a,b] => eval env a `mod` eval env b
--         _     => 0
--
--     Neg =>
--       case args of
--         [a] => negate (eval env a)
--         _   => 0
--
--     Not =>
--       case args of
--         [a] => if eval env a == 0 then 1 else 0
--         _   => 0
--
--     Equal =>
--       case args of
--         [a,b] => if eval env a == eval env b then 1 else 0
--         _     => 0
--
--     NotEqual =>
--       case args of
--         [a,b] => if eval env a /= eval env b then 1 else 0
--         _     => 0
--
--     Less =>
--       case args of
--         [a,b] => if eval env a < eval env b then 1 else 0
--         _     => 0
--
--     Greater =>
--       case args of
--         [a,b] => if eval env a > eval env b then 1 else 0
--         _     => 0
--
--     LessEqual =>
--       case args of
--         [a,b] => if eval env a <= eval env b then 1 else 0
--         _     => 0
--
--     GreaterEqual =>
--       case args of
--         [a,b] => if eval env a >= eval env b then 1 else 0
--         _     => 0
--
--     And =>
--       case args of
--         [a,b] => if eval env a /= 0 && eval env b /= 0 then 1 else 0
--         _     => 0
--
--     Or =>
--       case args of
--         [a,b] => if eval env a /= 0 || eval env b /= 0 then 1 else 0
--         _     => 0

findLabel : Identifier -> List Stmt -> Nat -> Maybe Nat
findLabel _ [] _ = Nothing

findLabel name (StmtLabel l :: xs) i =
  if name == l then Just i
  else findLabel name xs (i + 1)

findLabel name (_ :: xs) i =
  findLabel name xs (i + 1)

exec : List Stmt -> Env -> Nat -> IO ()
exec code env pc = do
  -- putStrLn ("PC = " ++ show pc)

  if pc >= length code
    then do
    -- putStrLn "HALT (pc out of bounds)"
    pure ()
    else
      case getAt pc code of

        Nothing => do
          -- putStrLn "HALT (Nothing at pc)"
          pure ()

        Just stmt => do
          -- putStrLn ("STM = " ++ show stmt)

          case stmt of

            StmtAssign x e => do
              let v = eval env e
              -- putStrLn ("ASSIGN " ++ x ++ " = " ++ show v)
              let env' = setVar x v env
              exec code env' (pc + 1)

            StmtPrint e => do
              let v = eval env e
              -- putStrLn ("PRINT = " ++ show v)
              printLn (pack . filter ('"' /=) . unpack . show $ v)
              exec code env (pc + 1)

            StmtLabel l => do
              -- putStrLn ("LABEL " ++ l)
              exec code env (pc + 1)

            StmtIf cond label => do
              let v = eval env cond
              -- putStrLn ("IF cond = " ++ show v ++ " goto " ++ label)

              if v /= 0 then
                case findLabel label code 0 of
                  Just target => do
                    -- putStrLn ("JUMP to " ++ show target)
                    exec code env target

                  Nothing => do
                    -- putStrLn ("LABEL NOT FOUND: " ++ label)
                    exec code env (pc + 1)
                else do
                  -- putStrLn "IF FALSE"
                  exec code env (pc + 1)

            StmtGoto label => do
              -- putStrLn ("GOTO " ++ label)

              case findLabel label code 0 of
                Just target => do
                  -- putStrLn ("JUMP to " ++ show target)
                  exec code env target

                Nothing => do
                  -- putStrLn ("LABEL NOT FOUND: " ++ label)
                  exec code env (pc + 1)

