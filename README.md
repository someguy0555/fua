# BNF
```EBNF

<expr>       := equality;
<equality>   := comparison ( ( "==" "!=" ) comparison )*;
<comparison> := logical ( ( "<" "<=" ">" ">=" ) logical )*;
<logical>    := term ( ( "&&" "||" ) term )*;
<term>       := factor ( ( "+" "-" ) factor)*;
<factor>     := unary ( ( "*" "/" "%" ) unary )*;
<unary>      := ( "!" | "-" ) unary | primary;
<primary>    := <number> | <identifier> | "(" <expr> ")";

```

# Examples

```

New: Type = Nil | Int
Two: Type = Bool | Nil

Nil = nil
Bool = true | false
Nat = Zero | Suc Nat
Int = ... | -1 | 0 | 1 | ...
Real = ? Some bullshit ?

Type -> Type
Tuple Type Type
Table {
    name: String,
    surname: String,
    age: Nat
}

main : Env Int = {
}

main : State { state = Table { ... }, return = Nil }

add : Int -> Int -> Int
add : Int -> Int -> State { state = Table { Int, Int, ... }, return Int }

a: Int
b: Int
a_plus_b : Int = { return a + b }

Coords = Table {
    x: Int,
    y: Int
}

while { a < b } {
    c = c
}

a = length $ for _ in [1..100) { inc = inc + 1 }
-- a : Int = 99

for [1..10] (\i => { sum = sum + i })

main = {
    line = get
    return a_plus_b
}

class Show(T: Type)
{
    show : T -> String
}

NewType (Type -> Type -> Constraint)
type Either(E: Type, T: Type) { Left E | Right T }

instance Show (List (implements Show))
{
    fn show(ls) {
        strs = map (show) ls
        return $ "[" ++ (con "," strs) ++ "]"
    }
}

main = \a: Int, b: Int => { return a + b }


```

```
type Maybe(T: Type) { Just T | Nothing }

maybe: Maybe Int = Just 5

match maybe {
    Just x => { print . show $ x; exit; },
    Nothing => { exit }
}

class Show(T: Type) {
    show : T -> String
}

class Collection(T: Type -> Type)
{
    has_next: Bool
    next: T
    remove: Nil
}

type List(T: Type) { End | Cons T (List T) }

fn add_one(ls: List Int) {
    return match ls {
        End       => End,
        Cons x xs => Cons (x + 1) (add_one xs)
    }
}

add_one [1..10]
==> [2..11]

class Functor(F: Type -> Type) {
    fmap : (A -> B) -> F A -> F B
}

add : Num A => A -> A -> A

i = -10
while i < 0 {
    print i
    i = i + 1
}

type List(T: Type) {
    [],
    (:) T (List T)
}

type Either(E: Type, T: Type) {
    Left E,
    Right T
}

type Nat {
    Z,
    S Nat
}

type Tuple(T: Type, U: Type)
{
    Tuple T U
}

type Tuple T U { Tuple T U }

table: { x: Int, y: Int } = { x = 0, y = 5 }

table = {
    x: Nat = 0,
    y: Nat = 5
}

ay: Tuple Int Int = Tuple 2 3

```

```
type List T { End, Cons T (List T) }

class Functor() {
    fmap: (a -> b) -> f a -> f b
}

{-
    foldl: { Traversable t } => (b -> a -> b) -> b -> t a -> b
    fn foldl f acc tr {
    }

    fn foldl { Traversable t } => ()
-}

instance Functor ls {
    fn fmap(f, a) {
        return match a {
            []    => [],
            x::xs => fmap f xs
        }
    }
}

fmap (show)

```

```
type List(T: Type) { End, Cons T (List T) }

ints: List Int = Cons 1 . Cons 2. Cons 3 $ End

sum = \ls => {
    match ls {
        Cons x End => { return x },
        Cons x xs  => { return x + (recurse 1 xs) }
    }
}

```

```
type Kind = { Type, Kind -> Kind }

type Nil = { nil }
type Bool = { true, false }
type Nat = { 0, s Nat }
type Int = { .. -1, 0, 1 .. }
type Real = { ... }

type Either(E: Type, T: Type) { left E, right T }

fn add(a, b) { return a + b }

sub : Int -> Int -> Int
fn sub(a, b) { return a - b }

fib: Nat -> Nat
fn fib(nth) {
    return if nth < 2 {
        return nth
    } else {
        nth -= 1
        a = 0
        b = 1
        while 0 < nth {
            c = a + b
            a = b
            b = c
            --nth
        }
        return c
    }
}

fn even(e) { return i % 2 == 0 }
main = {
    even_sum = filter_nil $ for i in [1..10) {
        return if even i { return i }
            else { return nil }
    }
    print even_sum
}

```

```
-- Module system
M = {}
type M.Either(E: Type, T: Type) { left E, right T }

M.type_info: Type -> String
fn M.type_info(T) { show T }

return M

-- Import system

M = import.path = "./module.stua"
std = import.module "std"

file = std.io.open "file.txt"

a = read.all $ file

fn add_string(a: String, b: String) Maybe Int {
    match to_int a {
        nothing => nothing,
        just ia  => match {
            nothing => nothing,
            just ib => just $ ia + ib
        }
    }
}

```


# Versions
* Version 1 - basic type system, no typeclasses or anything.
```
-- Subset

-- This 
type Type = { Type, Type -> Type } -- Type -> Type: Type is not the constructor, but the type itself

-- Basic types
type Nil = { nil }
type Bool = { true, false }
type Nat = { 0, s Nat }
type Int = { .. -1, 0, 1 .. }
type Real = { ... }

-- Derivative types
type [](T: Type) { [], T :: [T] }
type (,)(A: Type, B: Type) { (A,B) }
type {...} {...} -- some bullshit, idk

-- block
{
    stmt1,
    stmt2,
    ...,
    stmt -- This last statement is the return statement
}

-- Basic control flow - expressions
if ..bool.. {} else {} -- 
while ..bool.. {}

-- For now, without typeclasses, we can have operator overloading for the few basic types.
-- This could be replaced as an operation between things of the same typeclasss

-- Declarations, assignment
-- 1.
a: <Type> = <value>
-- 2.
a: <Type>
a = <value>
-- 3.
a = <value> -- if type can be inferred

-- Funcion declarations, assignment
f1: <Type1> -> <Type2>
f1 = fn(t1) { ... } -- assingning lambda
fn f1(t1) { ... }
fn f2(t1: Type1) Type2 {}

```
* Version 2 - parametric polymorphism
```
this allows us to do stuff like this:
map: (a -> b) -> List a -> List b
fn map(f, la) {
    match la {
        [] => [],
        x::xs => f x ++ (map xs)
    }
}

```
* Version 3 - typeclasses and typeclass constraints
```
class Show(a: Type) {
    show: a -> String
}

class Functor(f: Type -> Type) {
    fmap : (a -> b) -> f a -> f b
}

type List(a: Type) {
    [],
    a :: (List a)
}

type Either(a: Type, b: Type) { left a, right b }

Functor List = {
    fn fmap(f, la) {
        match la {
            [] => [],
            x::xs => f x :: (f xs)
        }
    }


type Ordering { LT, EQ, GT }
class Ord(a: Type) {
    cmp : a -> a -> Ordering
}

type RPS { Rock, Paper, Scissors }

instance Ord RPS {
    fn cmp(a, b) {
        match a {
            Rock     => match {
                Rock     => EQ,
                Paper    => LT,
                Scissors => GT
            },
            Paper    => match {
                Rock     => GT,
                Paper    => EQ,
                Scissors => LT
            },
            Scissors => match {
                Rock     => LT,
                Paper    => GT,
                Scissors => EQ
            },
        }
    }
}



```
