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
