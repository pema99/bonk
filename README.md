# Bonk
Bonk, son of [Gunk](https://github.com/pema99/gunk), cousin of [Plonk](https://github.com/pema99/plonk).
Yet another toy language I started working on, mainly to play with Hindley-Milner type inference. Bonk is a functional language with the goal of having very few abstractions while still being somewhat usable. It can be interpreted or compiled to JavaScript.

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
- Purity analysis. All functions which have side effects must be annotated as impure.
- A _very_ work-in-progress implementation of typeclasses for ad-hoc polymorphism.
- List literals as syntax sugar for `Cons`-lists.
- Pipeline operators for function application: `|>`, `<|`.
- Import statements to work with programs spanning multiple files.
- An automatic memoization keyword for pure functions.
- A tiny standard library (see `lib/bonk/prelude.bonk`).

# Example code
I solved quite a few problems from Advent of Code 2022 using bonk, [view the solutions here](https://github.com/pema99/bonk/tree/master/examples/aoc2022).

I've also [implemented a few common persistent data structures](https://github.com/pema99/bonk/blob/master/examples/data_structures.bonk) including heaps, stacks, queues, and AA trees (similar to red-black trees).

Other than that, the following program typechecks and runs. Syntax subject to change.
```fs
// Bonk ships with a small standard library.
// Let's use it to calculate the sum of the 20 first square numbers which are even:
let total =
    let first20 = iota 20 in
    let squares = map ([x] x * x) first20 in
    let evens = filter ([x] x % 2 = 0) squares in
    fold (+) 0 evens
in

// We can do the same thing more succintly with the pipeline operator.
// Bonk supports shadowing, so we can shadow the previous binding:
let total =
    iota 20
    |> map ([x] x * x)
    |> filter ([x] x % 2 = 0)
    |> fold (+) 0
in

// Bonk supports sum types:
sum MyList 'a =
    | MyNil unit
    | MyCons 'a * MyList 'a

// ... and recursive functions, which go well together:
rec makeList = [n]
    if n < 0 then MyNil ()
    else MyCons (n, makeList (n - 1))
in

rec sumList = [lst]
    match lst with
    | MyNil _ -> 0
    | MyCons (x, xs) -> x + sumList xs
in

// Let's print out some results:
let total2 = sumList (makeList 10) in
let _ = printfn total in
let _ = printfn total2 in
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
