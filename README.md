# Bonk
Bonk, son of [Gunk](https://github.com/pema99/gunk), cousin of [Plonk](https://github.com/pema99/plonk).
Yet another toy language I started working on, mainly to play with Hindley-Milner type inference. Bonk is a purely functional language with the goal of having very few abstractions while still being somewhat usable. It is currently either interpreted or compiled to JavaScript.

# Features
- Basic expressions. IE. `if`, `let`, function application and abstraction, arithmetic.
- Algebraic datatypes: Tuples and user-defined discriminated unions.
- Full type inference. Types of expressions can be inferred without any type annotations.
- ML-style match expressions with exhaustiveness checking.
- Pattern matching both in `let` and `match` constructs, as well as in inputs to lambdas.
- Parametric polymorphism. Functions can be generic.
- A working interpreter/REPL that also provides type information.
- A [JavaScript backend](https://gist.github.com/pema99/935b915a3197b5222183bf6ac4bb8308).
- JavaScript interop via raw-JavaScript expression blocks.
- Recursion (including mutual recursion) is supported, with tail call optimization.
- A _very_ work-in-progress implementation of typeclasses for ad-hoc polymorphism.
- List literals as syntax sugar for `Cons`-lists.
- Pipeline operators for function application: `|>`, `<|`.
- Import statements to work with programs spanning multiple files.
- A tiny standard library (see `lib/bonk/prelude.bonk`).

# Example code
The following program typechecks and runs. Syntax subject to change.
```fs
// Bonk supports sum types.
sum List 'a =
    | Cons 'a * List 'a
    | Nil unit

// And recursive functions, though functions are just named lambdas.
// The 'rec' keyword is used to denote that a function is recursive.
rec map = [f] [lst]
    match lst with
    | Cons (h, t) -> Cons (f h, map f t)
    | Nil _       -> Nil () 
in

rec fold = [f] [z] [lst]
    match lst with
    | Cons (h, t) -> f (h) (fold f z t)
    | Nil _       -> z
in

// There is small standard library with functions like 'iota' and 'filter'.
// Let's use them to calculate the sum of the 20 first square numbers which are even:
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
- Type ascription

# Fluff
- Dependencies are cringe.
- Damn, I've really been getting a lot of use out my crappy parser combinator library lately. Wew lad.
- His palms are sweaty.
- Knees weak.
- Arms spaghetti.
