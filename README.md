# Bonk
Bonk, son of [Gunk](https://github.com/pema99/gunk), cousin of [Plonk](https://github.com/pema99/plonk).
Yet another toy language I started working on, mainly to play with Hindley-Milner type inference. Bonk is a purely functional language with the goal of having very few abstractions while still being somewhat usable.

# Features
- Basic expressions. IE. `if`, `let`, function application and abstraction, arithmetic
- Algebraic datatypes: Tuples and user-defined discriminated unions.
- Full type inference. Types of expressions can be inferred without any type annotations.
- ML-style match expressions
- Pattern matching both in `let` and `match` constructs.
- Polymorphism. Functions can be generic.
- Recursion via a fixed-point combinator named `rec`.
- _Everything_ is an expression. Thus, an entire program is a single expression.
- An working interpreter/REPL that also provides type information.
- A tiny standard library (see `lib/prelude.bonk`).

# Example code
The following program typechecks and runs. Syntax subject to change.
```fs
sum List 'a =
    | Cons 'a * List 'a
    | Nil unit
in

let map = rec [map] [f] [lst]
    match lst with
    | Cons (h, t) -> Cons (f h, map f t)
    | Nil _       -> Nil () 
in

let fold = rec [fold] [f] [z] [lst]
    match lst with
    | Cons (h, t) -> f (h) (fold f z t)
    | Nil _       -> z
in

let myList = Cons (1, Cons (2, Cons (3, Nil ()))) in

let r1 = map ([x] x * 5) myList in
let r2 = fold ([x] [y] x + y) 0 r1 in
r2
```
Check the examples folder for more examples.

# How to build
Requires dotnet core:
```sh
git clone https://github.com/pema99/bonk
cd bonk
git submodule update --init --recursive
dotnet run
```

# Fluff
- Dependencies are cringe.
- Damn, I've really been getting a lot of use out my crappy parser combinator library lately. Wew lad.
- His palms are sweaty.
- Knees weak.
- Arms spaghetti.
