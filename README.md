# Bonk
Bonk, son of [Gunk](https://github.com/pema99/gunk), cousin of [Plonk](https://github.com/pema99/plonk).
Yet another toy language I started working on, mainly to play with Hindley-Milner type inference. Bonk is a purely functional language with the goal of having very few abstractions while still being somewhat usable. It is currently only interpreted, but I might implement a bytecode VM at some point.

# Features
- Basic expressions. IE. `if`, `let`, function application and abstraction, arithmetic
- Algebraic datatypes: Tuples and user-defined discriminated unions.
- Full type inference. Types of expressions can be inferred without any type annotations.
- ML-style match expressions
- Pattern matching both in `let` and `match` constructs.
- Parametric polymorphism. Functions can be generic.
- Recursion via a fixed-point combinator named `rec`.
- A _very_ work-in-progress implementation of typeclasses.
- An working interpreter/REPL that also provides type information.
- A tiny standard library (see `lib/prelude.bonk`).

# Example code
The following program typechecks and runs. Syntax subject to change.
```fs
// Bonk supports sum types.
sum List 'a =
    | Cons 'a * List 'a
    | Nil unit

// And recursive functions, though functions are just named lambdas.
let rec map = [f] [lst]
    match lst with
    | Cons (h, t) -> Cons (f h, map f t)
    | Nil _       -> Nil () 
in

let rec fold = [f] [z] [lst]
    match lst with
    | Cons (h, t) -> f (h) (fold f z t)
    | Nil _       -> z
in

// There is small standard library with functions like 'iota' and 'filter'.
// Let's use them to calculate the sub of the 20 first square numbers which are even:
let myList = iota 20 in
let r1 = map ([x] x * x) myList in
let r2 = filter ([x] x % 2 = 0) r1 in
let r3 = fold (+) 0 r2 in
r3
```
Check the examples folder for more examples.

# How to build
To build, you need dotnet core installed. Then run:
```sh
git clone https://github.com/pema99/bonk
cd bonk
git submodule update --init --recursive
dotnet run
```
To run tests, you can do:
```sh
dotnet run test
```
And to bless tests (accept current output as correct), do:
```sh
dotnet run bless
```

# To do (maybe, stuff I'm looking at)
- Rust-style traits/typeclasses for ad-hoc polymorphism
- Exhaustiveness checking for pattern matching
- Type ascription

# Fluff
- Dependencies are cringe.
- Damn, I've really been getting a lot of use out my crappy parser combinator library lately. Wew lad.
- His palms are sweaty.
- Knees weak.
- Arms spaghetti.
