# Bonk
Bonk, son of [Gunk](https://github.com/pema99/gunk), cousin of [Plonk](https://github.com/pema99/plonk).
Yet another shitty toy language I started working on, mainly to play with Hindley-Milner type inference.

# How to build
Requires dotnet core:
```sh
git clone https://github.com/pema99/bonk
cd bonk
git submodule update --init --recursive
dotnet run
```

# Example code (syntax subject to change)
This currently typechecks and runs:
```fs
let add = [x] [y] x + y in
let mul = [x] [y] x * y in
let compose = [f] [g] [l] f (g l) in
compose (add 5) (mul 2) 10
```
# Fluff
- Dependencies are cringe.
- Damn, I've really been getting a lot of use out my crappy parser combinator library lately. Wew lad.
- His palms are sweaty.
- Knees weak.
- Arms spaghetti.
