module Pipeline

open System.IO
open Repr
open Parse
open Combinator
open Inference
open Prelude
open Lower
open CodeGen
open Semantics
open Lex

let loadCodeFile (from: string) (path: string) : string =
    let fromPath = if from = "" then "" else Path.GetDirectoryName from
    let fullPath = Path.Combine(fromPath, path)
    if File.Exists fullPath then
        File.ReadAllText fullPath
    else if File.Exists path then
        File.ReadAllText path
    else
        match Map.tryFind path builtinFiles with
        | Some code -> code
        | _ -> failwith <| sprintf "File '%s' not found.\n" path

let resolveImports prelude files =
    // Handle prelude and intrinsics
    let preimport =
        if prelude
        then ["lib/bonk/builtins_js.bonk"; "lib/bonk/prelude.bonk"]
        else ["lib/bonk/builtins_js.bonk"]
    let visited = preimport |> List.map (fun file -> file, loadCodeFile "" file) |> Map.ofList
    let files = Seq.append preimport files
    // Recursive walk of imports
    let rec walkImports from visited acc file =
        if Map.tryFind file visited |> Option.isSome then
            visited, acc
        else
            let content = loadCodeFile from file
            let visited = Map.add file content visited
            match parseImports content with
            | Ok imports ->
                imports |> List.fold (
                    fun (visited, acc) file ->
                        walkImports from visited acc file
                    ) (visited, acc @ (imports @ [file]))
            | _ -> visited, acc
    let (visited, files) =
        files
        |> Seq.fold (fun (visited, acc) file -> walkImports file visited acc file) (visited, preimport)
    List.distinct files
    |> List.map (fun file -> Map.find file visited)

let pipeline prelude =
    resolveImports prelude
    >> parsePrograms
    >> Result.bind inferPrograms
    >> Result.bind checkPrograms
    >> Result.map lowerPrograms
    >> Result.map emitPrograms

let startCompile prelude output files =
    match pipeline prelude files with
    | Ok js -> File.WriteAllText(output, js)
    | Error err -> printfn "%s" err

