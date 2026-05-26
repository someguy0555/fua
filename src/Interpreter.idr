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
-- import Theorem

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

eval : Env -> Expr -> Integer
eval env (ExprOperand n) = n

eval env (ExprVariable x) = getVar x env

eval env (ExprOperator op args) =
  case op of
    Add =>
      case args of
        [a,b] => eval env a + eval env b
        _     => 0

    Sub =>
      case args of
        [a,b] => eval env a - eval env b
        _     => 0

    Mul =>
      case args of
        [a,b] => eval env a * eval env b
        _     => 0

    Div =>
      case args of
        [a,b] => eval env a `div` eval env b
        _     => 0

    Mod =>
      case args of
        [a,b] => eval env a `mod` eval env b
        _     => 0

    Neg =>
      case args of
        [a] => negate (eval env a)
        _   => 0

    Not =>
      case args of
        [a] => if eval env a == 0 then 1 else 0
        _   => 0

    Equal =>
      case args of
        [a,b] => if eval env a == eval env b then 1 else 0
        _     => 0

    NotEqual =>
      case args of
        [a,b] => if eval env a /= eval env b then 1 else 0
        _     => 0

    Less =>
      case args of
        [a,b] => if eval env a < eval env b then 1 else 0
        _     => 0

    Greater =>
      case args of
        [a,b] => if eval env a > eval env b then 1 else 0
        _     => 0

    LessEqual =>
      case args of
        [a,b] => if eval env a <= eval env b then 1 else 0
        _     => 0

    GreaterEqual =>
      case args of
        [a,b] => if eval env a >= eval env b then 1 else 0
        _     => 0

    And =>
      case args of
        [a,b] => if eval env a /= 0 && eval env b /= 0 then 1 else 0
        _     => 0

    Or =>
      case args of
        [a,b] => if eval env a /= 0 || eval env b /= 0 then 1 else 0
        _     => 0

------------------------------------------------------------
-- TYPED STATE MACHINE
------------------------------------------------------------

data EvalStep : Type where
  StepEval : Env -> Expr -> EvalStep

data Frame
  = EvalR Expr
  | EvalOp2L (Integer -> Integer -> Integer) Expr
  | EvalOp2R (Integer -> Integer -> Integer) Integer

data EvalState
  = Running Env Expr (List Frame)
  | Done Env Integer

unwind : Env -> Integer -> List Frame -> EvalState
step : EvalState -> EvalState
evalExpr : Env -> Expr -> Integer
runExpr : Env -> Expr -> Integer

step (Done env v) = Done env v

-- Evaluate a literal
step (Running env (ExprOperand n) stack) =
  case stack of
    [] => Done env n
    _  => unwind env n stack

-- Evaluate variable
-- step (Running env (ExprVariable x) stack) =
--   let v =
--         case SortedMap.lookup x env.symbols of
--           Just (Var v') =>
--             trace ("EVAL VAR " ++ show x ++ " = " ++ show v') v'
--           Just Label =>
--             trace ("EVAL LABEL " ++ show x) 0
--           Nothing =>
--             trace ("EVAL MISS " ++ show x) 0
--   in
--     case stack of
--       [] => Done env v
--       _  => unwind env v stack
step (Running env (ExprVariable x) stack) =
  let v =
        case SortedMap.lookup x env.symbols of
          Just (Var v') => v'
          Just Label     => 0
          Nothing  => 0
  in
    case stack of
      [] => Done env v
      _  => unwind env v stack


-- Operator application (dispatch)
step (Running env (ExprOperator op args) stack) =
  case op of

    Add =>
      case args of
        [a,b] => -- trace ("ADD: " ++ show a ++ " + " ++ show b)
                 Running env a (EvalOp2L (+) b :: stack)
        _     => Done env 0

    Sub =>
      case args of
        [a,b] => Running env a (EvalOp2L (-) b :: stack)
        _     => Done env 0

    Mul =>
      case args of
        [a,b] => Running env a (EvalOp2L (*) b :: stack)
        _     => Done env 0

    Div =>
      case args of
        [a,b] => Running env a (EvalOp2L div b :: stack)
        _     => Done env 0

    Mod =>
      case args of
        [a,b] => Running env a (EvalOp2L mod b :: stack)
        _     => Done env 0

    Neg =>
      case args of
        [a] => Running env a (EvalOp2L (\x, y => 0 - x) (ExprOperand 0) :: stack)
        _   => Done env 0

    Not =>
      case args of
        [a] => Running env a (EvalOp2L (\x, _ => if x == 0 then 1 else 0) (ExprOperand 0) :: stack)
        _   => Done env 0

    Equal =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x == y then 1 else 0) b :: stack)
        _     => Done env 0

    NotEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= y then 1 else 0) b :: stack)
        _     => Done env 0

    Less =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x < y then 1 else 0) b :: stack)
        _     => Done env 0

    Greater =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x > y then 1 else 0) b :: stack)
        _     => Done env 0

    LessEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x <= y then 1 else 0) b :: stack)
        _     => Done env 0

    GreaterEqual =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x >= y then 1 else 0) b :: stack)
        _     => Done env 0

    And =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= 0 && y /= 0 then 1 else 0) b :: stack)
        _     => Done env 0

    Or =>
      case args of
        [a,b] => Running env a (EvalOp2L (\x, y => if x /= 0 || y /= 0 then 1 else 0) b :: stack)
        _     => Done env 0

-- unwind env v [] = Done env v
--
-- unwind env v (EvalOp2L f rhs :: stack) =
--   Running env rhs (EvalOp2R f v :: stack)
--
-- unwind env v (EvalOp2R f v1 :: stack) =
--   let v' = f v1 v
--   in unwind env v' stack
--
-- unwind env v (EvalR e :: stack) =
--   Running env e (EvalOp2R (\x, y => x) v :: stack)
unwind env v [] =
  Done env v

unwind env v (EvalOp2L f rhs :: stack) =
  Running env rhs (EvalOp2R f v :: stack)

unwind env v (EvalOp2R f vLeft :: stack) =
  let result = f vLeft v
  in unwind env result stack

unwind env v (EvalR e :: stack) =
  Running env e (EvalOp2R (\x, y => x) v :: stack)

-- evalExpr env e =
--   case step (Running env e []) of
--     Done _ v => v
--     Running env' e' st => evalExpr env' e'

runExpr env e = go (Running env e [])
  where
    go : EvalState -> Integer
    go (Done _ v) = v
    go st = go (step st)

------------------------------------------------------------
-- PUBLIC INTERFACE (STATE MACHINE WRAPPER)
------------------------------------------------------------

export
data ExprRunState
  = ER Env Expr
  | ED Env Integer

export
stepExpr : ExprRunState -> ExprRunState
stepExpr (ED env v) = ED env v
stepExpr (ER env e) =
  case step (Running env e []) of
    Done env' v => ED env' v
    Running env' e' st =>
      case st of
        [] => ER env' e'
        _  => ER env' e'

export
runExprState : Env -> Expr -> Integer
runExprState env e = go (ER env e)
  where
    go : ExprRunState -> Integer
    go (ED _ v) = v
    go s = go (stepExpr s)
------------------------------------------------------------
-- ENV - EXPR ENV BRIDGE
------------------------------------------------------------

-- extractInts : SortedMap Identifier SymType -> SortedMap Identifier Integer
-- extractInts m = go (toList m) empty
--   where
--     go : List (Identifier, SymType) ->
--          SortedMap Identifier Integer ->
--          SortedMap Identifier Integer
--     go [] acc = acc
--
--     go ((k, Var v) :: xs) acc =
--       go xs (insert k v acc)
--
--     go ((_ , Label) :: xs) acc =
--       go xs acc
--
-- toExprEnv : Env -> ExprEnv
-- toExprEnv env = MkExprEnv (extractInts (symbols env))

------------------------------------------------------------
-- REST
------------------------------------------------------------

findLabel : Identifier -> List Stmt -> Nat -> Maybe Nat
findLabel _ [] _ = Nothing

findLabel name (StmtLabel l :: xs) i =
  if name == l then Just i
  else findLabel name xs (i + 1)

findLabel name (_ :: xs) i =
  findLabel name xs (i + 1)

-- exec : List Stmt -> Env -> Nat -> IO ()
-- exec code env pc = do
--   -- putStrLn ("PC = " ++ show pc)
--
--   if pc >= length code
--     then do
--     -- putStrLn "HALT (pc out of bounds)"
--     pure ()
--     else
--       case getAt pc code of
--
--         Nothing => do
--           -- putStrLn "HALT (Nothing at pc)"
--           pure ()
--
--         Just stmt => do
--           -- putStrLn ("STM = " ++ show stmt)
--
--           case stmt of
--
--             StmtAssign x e => do
--               let v = eval env e
--               -- putStrLn ("ASSIGN " ++ x ++ " = " ++ show v)
--               let env' = setVar x v env
--               exec code env' (pc + 1)
--
--             StmtPrint e => do
--               let v = eval env e
--               -- putStrLn ("PRINT = " ++ show v)
--               printLn (pack . filter ('"' /=) . unpack . show $ v)
--               exec code env (pc + 1)
--
--             StmtLabel l => do
--               -- putStrLn ("LABEL " ++ l)
--               exec code env (pc + 1)
--
--             StmtIf cond label => do
--               let v = eval env cond
--               -- putStrLn ("IF cond = " ++ show v ++ " goto " ++ label)
--
--               if v /= 0 then
--                 case findLabel label code 0 of
--                   Just target => do
--                     -- putStrLn ("JUMP to " ++ show target)
--                     exec code env target
--
--                   Nothing => do
--                     -- putStrLn ("LABEL NOT FOUND: " ++ label)
--                     exec code env (pc + 1)
--                 else do
--                   -- putStrLn "IF FALSE"
--                   exec code env (pc + 1)
--
--             StmtGoto label => do
--               -- putStrLn ("GOTO " ++ label)
--
--               case findLabel label code 0 of
--                 Just target => do
--                   -- putStrLn ("JUMP to " ++ show target)
--                   exec code env target
--
--                 Nothing => do
--                   -- putStrLn ("LABEL NOT FOUND: " ++ label)
--                   exec code env (pc + 1)

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
              let v = runExpr env e
              -- putStrLn ("ASSIGN " ++ x ++ " = " ++ show v)
              let env' = setVar x v env
              exec code env' (pc + 1)

            StmtPrint e => do
              let v = runExpr env e
              -- putStrLn ("PRINT = " ++ show v)
              printLn (pack . filter ('"' /=) . unpack . show $ v)
              exec code env (pc + 1)

            StmtLabel l => do
              -- putStrLn ("LABEL " ++ l)
              exec code env (pc + 1)

            StmtIf cond label => do
              let v = runExpr env cond
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
