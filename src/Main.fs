module Main

open Repl
open CodeGen
open Tests

let printHelp() =
    printfn "Usage: bonk <command> options..."
    printfn ""
    printfn "Commands:"
    printfn "   repl                Start the bonk REPL."
    printfn "   compile <files>     Compile bonk source files to JavaScript."
    printfn "   test                Run all tests."
    printfn "   bless               Bless current output of tests as correct."
    printfn "   help <command>      Print help about a command and exit."
    printfn ""
    printfn "Options"
    printfn "   -h  --help <cmd>    Print help and exit."

let printReplHelp() =
    printfn "Usage: bonk repl options..."
    printfn ""
    printfn "Options:"
    printfn "   --nobuiltins        Don't load builtin bindings / intrinsics."
    printfn "   --nostdlib          Don't load the standard library."

[<EntryPoint>]
let main args =
    if args.Length = 0 then
        printHelp()
    else if args.[0] = "help" || args.[0] = "-h" || args.[0] = "--help" then
        if args.Length > 1 && args.[1] = "repl" then
            printReplHelp()
        else
            printHelp()
    else if args.[0] = "repl" then
        let builtins = not <| Seq.contains "--nobuiltins" args
        let stdlib = not <| Seq.contains "--nostdlib" args
        startRepl builtins (stdlib && builtins)
    else if args.[0] = "test" then
        startTests()
    else if args.[0] = "bless" then
        System.IO.Directory.Delete("tests/output", true)
        startTests()
    else if args.[0] = "compile" then
        let builtins = not <| Seq.contains "--nobuiltins" args
        let stdlib = not <| Seq.contains "--nostdlib" args
        let files = args |> Seq.tail |> Seq.filter (fun str -> str.[0] <> '-')
        //startCompile builtins (stdlib && builtins) files
        ()
    else
        printHelp()
    0