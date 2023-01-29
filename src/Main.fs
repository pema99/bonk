module Main

open Repl
open Pipeline
open Tests

let printHelp() =
    printfn "Usage: bonk <command> options..."
    printfn ""
    printfn "Commands:"
    printfn "   repl                Start the bonk REPL."
    printfn "   compile <files>     Compile bonk source files to JavaScript."
    printfn "   test                Run all tests."
    printfn "   bless               Bless current output of tests as correct."
    printfn "   mermaid <file>      Generate a mermaid graph of from a bonk file."
    printfn "   help <command>      Print help about a command and exit."
    printfn ""
    printfn "Options:"
    printfn "   -h  --help <cmd>    Print help and exit."
    printfn ""

let printReplHelp() =
    printfn "Usage: bonk repl options..."
    printfn ""
    printfn "Options:"
    printfn "   --nobuiltins        Don't load builtin bindings / intrinsics."
    printfn "   --nostdlib          Don't load the standard library."
    printfn ""

let printCompileHelp() =
    printfn "Usage: bonk compile options... <files>"
    printfn ""
    printfn "Options:"
    printfn "   --output=<file>     Write compiled output to <file>."
    printfn "   --noprelude         Don't implicitly load the prelude."
    printfn ""

[<EntryPoint>]
let main args =
    if args.Length = 0 then
        printHelp()
    else if args.[0] = "help" || args.[0] = "-h" || args.[0] = "--help" then
        if args.Length > 1 && args.[1] = "repl" then
            printReplHelp()
        else if args.Length > 1 && args.[1] = "compile" then
            printCompileHelp()
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
        let prelude = not <| Seq.contains "--noprelude" args
        let output =
            args
            |> Seq.tryFind (fun str -> str.StartsWith "--output=")
            |> Option.map (fun str -> str.Split("=").[1])
            |> Option.defaultValue "out.js"
        let files = args |> Seq.tail |> Seq.filter (fun str -> str.[0] <> '-')
        if Seq.isEmpty files then
            printfn "Error: No files provided!"
            printCompileHelp()
        else
            startCompile prelude output files
    else if args.[0] = "mermaid" then
        Parse.parseProgram (System.IO.File.ReadAllText args.[1])
        |> Result.mapError (fun _ -> ())
        |> Result.map (fun p -> (snd >> snd) <| Pretty.prettyMermaidDecls p (0, ""))
        |> Result.map (Pretty.startMermaidPopup)
        |> ignore
    else
        printHelp()
    0