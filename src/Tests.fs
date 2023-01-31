module Tests

open ReprUtil
open Prelude
open Repl
open Monad
open Pretty

open System.IO
open System.Diagnostics
open System.Runtime.InteropServices
open System
open Pipeline

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

let fileExists filename =
    if File.Exists filename then true
    else
        let values = Environment.GetEnvironmentVariable "PATH"
        values.Split Path.PathSeparator
        |> Seq.exists(fun path -> File.Exists(Path.Combine (path, filename)))

let javaScriptRunner =
    ["bun"; "node"; "bun.exe"; "node.exe"; "nodejs.exe"]
    |> Seq.find fileExists

let testJS prelude file =
    // Compile program
    File.Delete "out.js"
    let inputPath = "tests/" + file + ".bonk"
    use sw = new StringWriter()
    let old = Console.Out
    Console.SetOut(sw)
    startCompile prelude "out.js" [inputPath]
    Console.SetOut(old)
    // Set up process
    use cmd = new Process()
    if RuntimeInformation.IsOSPlatform OSPlatform.Linux then
        cmd.StartInfo.FileName <- "/bin/sh"
    else
        cmd.StartInfo.FileName <- "cmd.exe"
        cmd.StartInfo.Arguments <- $"/C {javaScriptRunner} out.js"
    cmd.StartInfo.RedirectStandardInput <- true
    cmd.StartInfo.RedirectStandardOutput <- true
    cmd.StartInfo.RedirectStandardError <- true
    cmd.StartInfo.CreateNoWindow <- true
    cmd.StartInfo.UseShellExecute <- false
    // Run program
    cmd.Start() |> ignore
    if RuntimeInformation.IsOSPlatform OSPlatform.Linux then
        cmd.StandardInput.WriteLine($"{javaScriptRunner} out.js")
    cmd.StandardInput.Flush()
    cmd.StandardInput.Close()
    cmd.WaitForExit()
    // Compare output
    let stdout = cmd.StandardOutput.ReadToEnd()
    let err = sw.GetStringBuilder().ToString()
    let split =
        $"{stdout}\n{err}".Split([|"\r\n"; "\n"; "\r"|], StringSplitOptions.None)
        |> Seq.toList
    compareOrBless (file + "_compiled") (split)

let listTypes = repl {
    let! ((typeEnv, _, _, _), _, termEnv) = get
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

let findTests() =
    let rxMode = System.Text.RegularExpressions.Regex("//\s*Mode:\s*([A-Za-z, ]*)")
    let rxPrelude = System.Text.RegularExpressions.Regex("//\s*Prelude:\s*([A-Za-z]*)")
    let rxDesc = System.Text.RegularExpressions.Regex("//\s*Description:\s*([A-Za-z, #0-9]*)")
    let tests = 
        Directory.GetFiles("tests", "*.bonk")
        |> Seq.collect (fun path ->
            let fname = Path.GetFileNameWithoutExtension path
            let content = File.ReadAllText path
            let mode = if rxMode.Match(content).Groups.Count > 1 then rxMode.Match(content).Groups.[1].Value.ToLower() else "values"
            let prelude = if rxPrelude.Match(content).Groups.Count > 1 then rxPrelude.Match(content).Groups.[1].Value.ToLower() else "true"
            let prelude = if prelude = "true" then true else false
            let desc = if rxDesc.Match(content).Groups.Count > 1 then rxDesc.Match(content).Groups.[1].Value else fname
            let res = []
            let res = if mode.Contains "values"   then ($"{desc}, values", fun () -> testValues prelude fname)::res else res
            let res = if mode.Contains "types"    then ($"{desc}, types", fun () -> testTypes prelude fname)::res  else res
            let res = if mode.Contains "compiled" then ($"{desc}, compiled", fun () -> testJS prelude fname)::res     else res
            if List.isEmpty res then
                failwith <| sprintf "Invalid test mode '%s'." mode
            else
                res)
        |> Seq.toList
    ("Prelude types match", testPrelude) :: tests

let startTests() =
    printfn "Running tests..."
    let results = List.map (fun (name, body) ->
        match body() with
        | Ok () ->
            Console.ForegroundColor <- ConsoleColor.Green
            let res = sprintf "| %-50s | Pass" name
            printfn "%s" res
            Ok res
        | Error err ->
            Console.ForegroundColor <- ConsoleColor.Red
            let res = sprintf "| %-50s | Fail\n\t%s" name err
            printfn "%s" res
            Error res) (findTests())
    Console.ResetColor()
    let passed, failed =
        List.partition (fun x -> match x with Ok _ -> true | _ -> false) results
    printfn "Tests finished. Passed: %i, Failed: %i." (List.length passed) (List.length failed)