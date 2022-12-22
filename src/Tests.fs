module Tests

open Repr
open ReprUtil
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
                    let expected, actual =
                        List.find (fun (a, b) -> a <> b) (List.zip res content)
                    printfn "%A - %A" res content
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
                sprintf "%s : %s" name (prettyQualType ty)
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
    use sw = new StringWriter()
    let old = Console.Out
    Console.SetOut(sw)
    let res =
        match runReplAction prelude action with
        | Ok s -> compareOrBless (file + "_types") s
        | _ -> Error "Failed to run REPL action."
    Console.SetOut(old)
    res

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
    "Let polymorphism works for groups", fun () -> testTypes false "rec_let_polymorphism"
    "Simple value test", fun () -> testValues true "simple_value"
    "Simple typeclass test #1", fun () -> testTypes false "simple_typeclass_types"
    "Simple typeclass test #2", fun () -> testValues true "simple_typeclass_values"
    "Strange parsing edgecase", fun () -> testValues true "strange_parse"
    "Typeclass instance for constructed type", fun () -> testTypes false "typeclass_constructed_type"
    "Basic overload resolution works", fun () -> testValues true "overload_resolution"
    "Wrong typeclass implementation fails #1", fun () -> testValues false "typeclass_invalid"
    "Wrong typeclass implementation fails #2", fun () -> testValues false "typeclass_invalid_self"
    "Outdated environment regression", fun () -> testTypes false "outdated_env_bug"
    "Duplicate typeclass mentions", fun () -> testTypes false "duplicate_classes"
    "Two types, same typeclass", fun () -> testTypes false "two_types_same_typeclass"
    "Mutual recursion values", fun () -> testValues true "mutual_recursion"
    "Mutual recursion types", fun () -> testTypes true "mutual_recursion"
    "Simple raw black usage", fun () -> testTypes false "raw_blocks_simple"
    "Wide operators parse correctly", fun () -> testTypes false "wide_operator"
    "Typeclasses for polymorphic types", fun () -> testValues true "typeclass_polymorphic"
    "Missing typeclass causes error", fun () -> testValues true "typeclass_missing"
    "Invalid typeclass for polymorphic types", fun () -> testValues true "typeclass_polymorphic_invalid"
]

let findTests() =
    let rxMode = System.Text.RegularExpressions.Regex("//\s*Mode:\s*([A-Za-z, ]*)")
    let rxPrelude = System.Text.RegularExpressions.Regex("//\s*Prelude:\s*([A-Za-z]*)")
    let rxDesc = System.Text.RegularExpressions.Regex("//\s*Description:\s*([A-Za-z, ]*)")
    let tests = 
        Directory.GetFiles("tests", "*.bonk")
        |> Seq.collect (fun path ->
            let fname = Path.GetFileNameWithoutExtension path
            let content = File.ReadAllText path
            let mode = if rxMode.Match(content).Groups.Count > 1 then rxMode.Match(content).Groups.[1].Value.ToLower() else "values"
            let prelude = if rxPrelude.Match(content).Groups.Count > 1 then rxPrelude.Match(content).Groups.[1].Value.ToLower() else "true"
            let prelude = if prelude = "true" then true else false
            let desc = if rxDesc.Match(content).Groups.Count > 1 then rxDesc.Match(content).Groups.[1].Value else fname
            if mode.Contains "values" && mode.Contains "types" then
                [
                    desc + ", test types", fun () -> testTypes prelude fname
                    desc + ", test value", fun () -> testValues prelude fname
                ]
            else if mode.Contains "values" then
                [
                    desc, fun () -> testValues prelude fname
                ]
            else if mode.Contains "types" then
                [
                    desc, fun () -> testTypes prelude fname
                ]
            else
                failwith <| sprintf "Invalid test mode '%s'." mode
            )
        |> Seq.toList
    ("Prelude types match", testPrelude) :: tests

let startTests() =
    printfn "Running tests..."
    let results = List.map (fun (name, body) ->
        match body() with
        | Ok () ->
            Console.ForegroundColor <- ConsoleColor.Green
            let res = sprintf "| %-40s | Pass" name
            printfn "%s" res
            Ok res
        | Error err ->
            Console.ForegroundColor <- ConsoleColor.Red
            let res = sprintf "| %-40s | Fail\n\t%s" name err
            printfn "%s" res
            Error res) (findTests())
    Console.ResetColor()
    let passed, failed =
        List.partition (fun x -> match x with Ok _ -> true | _ -> false) results
    printfn "Tests finished. Passed: %i, Failed: %i." (List.length passed) (List.length failed)