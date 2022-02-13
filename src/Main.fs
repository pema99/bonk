module Main

open Repl
open Tests

[<EntryPoint>]
let main args =
    if args.Length > 0 && args.[0] = "test" then
        startTests()
    else if args.Length > 0 && args.[0] = "bless" then
        System.IO.Directory.Delete("tests/output", true)
        startTests()
    else
        startRepl()
    0