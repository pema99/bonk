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
            | Success imports ->
                imports |> List.fold (
                    fun (visited, acc) file ->
                        walkImports from visited acc file
                    ) (visited, acc @ (imports @ [file]))
            | err -> visited, acc
    let (visited, files) =
        files
        |> Seq.fold (fun (visited, acc) file -> walkImports file visited acc file) (visited, preimport)
    List.distinct files
    |> List.map (fun file -> Map.find file visited)

let startCompile prelude output files =
    let ast =
        files
        |> resolveImports prelude
        |> List.map parseProgram
        |> List.reduce (joinResult (fun a b -> a @ b))
    match ast with
    | Success decls ->
        let res, ((typeEnv,userEnv,classEnv,loc),_) =
            inferDecls decls ((funSchemes, Map.empty, classes, ((0,0),(0,0))), (Map.empty, 0))
        let res = Result.bind (checkMatches userEnv) res
        match res with
        | Ok decls ->
            let decls = lowerDecls decls
            let jsAst = List.collect emitDecl decls
            let jsOutput = pprJsBlock 0 jsAst
            let jsOutput = jsInstrincs + jsOutput
            File.WriteAllText(output, jsOutput)
        | Error err -> printfn "%s" err
    | Failure -> printfn "Parsing error: Unknown"
    | FailureWith (err, loc) -> printfn "Parsing error (%A): %s" loc err
    | CompoundFailure errs -> Seq.iter (fun (err, loc) -> printfn "Parsing error (%A): %s" loc err) errs
    ()