module Tests

open Repr
open Inference
open Prelude
open Parse
open Repr
open Repl
open Monad
open Pretty

open System.IO
open System

let compareOrBless name content =
    let path = "tests/output/" + name + ".expected"
    if File.Exists path then
        File.ReadAllLines path
        |> Seq.toList
        |> fun res ->
            if res = content then Ok ()
            else
                if List.length res = List.length content then
                    let actual, expected =
                        List.find (fun (a, b) -> a <> b) (List.zip res content)
                    Error (sprintf "Expected '%s' but got '%s'" expected actual)
                else
                    Error ("Outputs were different length")
    else
        if not <| Directory.Exists "tests/output" then
            ignore <| Directory.CreateDirectory "tests/output"
        File.WriteAllLines(path, content)
        Ok ()

let listTypes = repl {
    let! ((typeEnv, _, _, _), termEnv) = get
    let names = Map.toList typeEnv |> List.map fst
    return
        names
        |> List.map (fun name -> name, lookup typeEnv name)
        |> List.map (fun (name, ty) ->
            match ty with
            | Some (_, ty) ->
                sprintf "%s : %s" name (prettyQualType (renameFreshQualType ty))
            | _ ->
                sprintf "Invalid type for %s" name)
}

let testTypes prelude file =
    let inputPath = "tests/" + file + ".bonk"
    let action = repl {
        if prelude then do! loadLibrary true stdLib
        do! loadLibrary true (File.ReadAllText inputPath)
        return! listTypes
    }
    match runReplAction prelude action with
    | Ok s -> compareOrBless (file + "_types") s
    | _ -> Error "Failed to run REPL action."

let testValues prelude file =
    let inputPath = "tests/" + file + ".bonk"
    use sw = new StringWriter()
    let old = Console.Out
    Console.SetOut(sw)
    let action = repl {
        if prelude then do! loadLibrary true stdLib
        do! loadLibrary true (File.ReadAllText inputPath)
    }
    let res = runReplAction prelude action
    Console.SetOut(old)
    let split =
        sw.GetStringBuilder().ToString().Split([|"\r\n"; "\n"; "\r"|], StringSplitOptions.None)
        |> Seq.toList
    match res with
    | Ok s -> compareOrBless (file + "_values") (split)
    | _ -> Error "Failed to run REPL action."

let testPrelude() =
    let action = loadLibrary true stdLib >>. listTypes
    match runReplAction true action with
    | Ok s -> compareOrBless "prelude" s
    | _ -> Error "Failed to run REPL action."

let tests = [
    "Prelude types match", testPrelude
    "Let polymorphism works", fun () -> testTypes false "let_polymorphism"
    "Simple value test", fun () -> testValues true "simple_value"
    "Simple typeclass test #1", fun () -> testTypes false "simple_typeclass_types"
    "Simple typeclass test #2", fun () -> testValues true "simple_typeclass_values"
    "Strange parsing edgecase", fun () -> testValues true "strange_parse"
    "Typeclass instance for constructed type", fun () -> testTypes false "typeclass_constructed_type"
    "Basic overload resolution works", fun () -> testValues true "overload_resolution"
    "Wrong typeclass implementation fails #1", fun () -> testValues false "typeclass_invalid"
    "Wrong typeclass implementation fails #2", fun () -> testValues false "typeclass_invalid_self"
    "Outdated environment regression", fun () -> testTypes false "outdated_env_bug"
    "Mutual recursion values", fun () -> testValues true "mutual_recursion"
    "Mutual recursion types", fun () -> testTypes true "mutual_recursion"
]

let startTests() =
    let results = List.map (fun (name, body) ->
        match body() with
        | Ok () ->
            Ok <| sprintf "| %-40s | Pass" name
        | Error err ->
            Error <| sprintf "| %-40s | Fail\n\t%s" name err) tests
    printfn "Running tests..."
    for res in results do
        match res with
        | Ok s    -> 
            Console.ForegroundColor <- ConsoleColor.Green
            printfn "%s" s
        | Error s ->
            Console.ForegroundColor <- ConsoleColor.Red
            printfn "%s" s
    Console.ResetColor()
    let passed, failed =
        List.partition (fun x -> match x with Ok _ -> true | _ -> false) results
    printfn "Tests finished. Passed: %i, Failed: %i." (List.length passed) (List.length failed)