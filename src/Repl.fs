module Repl

open Repr
open Inference

// Eval
type Value =
    | VUnit
    | VInt of int
    | VBool of bool
    | VFloat of float
    | VString of string
    | VTuple of Value list
    | VClosure of Pat * Expr * TermEnv
    | VLazy of Value Lazy

and TermEnv = Map<string, Value>

let extendPat env pat v =
    match pat, v with
    | PName n, v -> extend env n v
    | PTuple n, VTuple v -> env
        // TODO: FIx
        //List.fold (fun acc (x, ve) -> extend acc x ve) env (List.zip n v)
    | _ -> env

let rec binop l op r =
    match l, op, r with
    | VInt l, Plus, VInt r -> Some <| VInt (l + r)
    | VInt l, Minus, VInt r -> Some <| VInt (l - r)
    | VInt l, Star, VInt r -> Some <| VInt (l * r)
    | VInt l, Slash, VInt r -> Some <| VInt (l / r)
    | VInt l, Equal, VInt r -> Some <| VBool (l = r)
    | VInt l, NotEq, VInt r -> Some <| VBool (l <> r)
    | VInt l, GreaterEq, VInt r -> Some <| VBool (l >= r)
    | VInt l, LessEq, VInt r -> Some <| VBool (l <= r)
    | VInt l, Greater, VInt r -> Some <| VBool (l > r)
    | VInt l, Less, VInt r -> Some <| VBool (l < r)
    | VFloat l, Plus, VFloat r -> Some <| VFloat (l + r)
    | VFloat l, Minus, VFloat r -> Some <| VFloat (l - r)
    | VFloat l, Star, VFloat r -> Some <| VFloat (l * r)
    | VFloat l, Slash, VFloat r -> Some <| VFloat (l / r)
    | VFloat l, Equal, VFloat r -> Some <| VBool (l = r)
    | VFloat l, NotEq, VFloat r -> Some <| VBool (l <> r)
    | VFloat l, GreaterEq, VFloat r -> Some <| VBool (l >= r)
    | VFloat l, LessEq, VFloat r -> Some <| VBool (l <= r)
    | VFloat l, Greater, VFloat r -> Some <| VBool (l > r)
    | VFloat l, Less, VFloat r -> Some <| VBool (l < r)
    | VString l, Plus, VString r -> Some <| VString (l + r)
    | VString l, Equal, VString r -> Some <| VBool (l = r)
    | VString l, NotEq, VString r -> Some <| VBool (l <> r)
    | VString l, GreaterEq, VString r -> Some <| VBool (l.Length >= r.Length)
    | VString l, LessEq, VString r -> Some <| VBool (l.Length <= r.Length)
    | VString l, Greater, VString r -> Some <| VBool (l.Length > r.Length)
    | VString l, Less, VString r -> Some <| VBool (l.Length < r.Length)
    | VBool l, And, VBool r -> Some <| VBool (l && r)
    | VBool l, Or, VBool r -> Some <| VBool (l || r)
    | _ -> None

and eval tenv e =
    match e with
    | Lit LUnit -> Some VUnit
    | Lit (LInt v) -> Some (VInt v)
    | Lit (LBool v) -> Some (VBool v)
    | Lit (LFloat v) -> Some (VFloat v)
    | Lit (LString v) -> Some (VString v)
    | Op (l, op, r) ->
        let v1 = eval tenv l
        let v2 = eval tenv r
        match v1, v2 with
        | Some v1, Some v2 -> binop v1 op v2
        | _ -> None
    | Var a -> lookup tenv a
    | App (f, x) ->
        let clos = eval tenv f
        let arg = eval tenv x
        match clos, arg with
        | Some (VClosure (a, body, env)), Some v ->
            let nenv = extendPat env a v 
            eval nenv body
        | Some (VLazy e), Some v -> // deferred application
            match e.Value with
            | VClosure (a, body, env) ->
                let nenv = extendPat env a v 
                eval nenv body
            | _ -> None
        | _ -> None
    | Lam (x, t) -> Some (VClosure (x, t, tenv))
    | Let (x, v, t) ->
        match eval tenv v with
        | Some ve ->
            let nenv = extendPat tenv x ve
            eval nenv t
        | _ -> None
    | If (c, tr, fl) ->
        match eval tenv c with
        | Some (VBool v) ->
            if v 
            then eval tenv tr
            else eval tenv fl 
        | _ -> None
    | Tup es ->
        let ev = List.map (eval tenv) es
        let ev = List.choose id ev
        if List.length es = List.length ev then Some (VTuple ev)
        else None
    | Rec e ->
        lazy (eval tenv (App (e, (Rec e))) |> Option.get)
        |> fun x -> Some (VLazy x)
    | _ -> None //TODO: Match and Sum

// Printing
let rec prettyValue v =
    match v with
    | VUnit -> "()"
    | VInt v -> string v
    | VBool v -> string v
    | VFloat v -> string v
    | VString v -> sprintf "%A" v
    | VTuple v -> sprintf "(%s)" <| String.concat ", " (List.map prettyValue v)
    | VClosure (a, _, _) -> "Closure"
    | VLazy _ -> "Lazy"

let printColor str =
    let rec cont str =
        match str with
        | h :: (t :: r) when h = '$' ->
                match t with
                | 'r' -> System.Console.ForegroundColor <- System.ConsoleColor.Red
                | 'g' -> System.Console.ForegroundColor <- System.ConsoleColor.Green
                | 'b' -> System.Console.ForegroundColor <- System.ConsoleColor.Blue
                | 'y' -> System.Console.ForegroundColor <- System.ConsoleColor.Yellow
                | _ -> System.Console.ForegroundColor <- System.ConsoleColor.White
                cont r
        | h :: t ->
                printf "%c" h
                cont t
        | _ -> ()
    cont (Seq.toList str)
    printfn ""
    System.Console.ForegroundColor <- System.ConsoleColor.White

// Repl start
open Combinator
open Parse

let mutable termEnv : TermEnv = Map.empty
let mutable typeEnv : TypeEnv = Map.empty
let mutable freshCount = 0

let extendTypeMany names ty =
    if not <| List.isEmpty names then
        match names, ty with
        | [name], ty ->
            typeEnv <- extend typeEnv name (ftvType ty |> Set.toList, ty)
        | names, TCtor (KProduct _, args) when List.length args = List.length names ->
            List.zip names args
            |> List.iter (fun (name, ty) ->
                typeEnv <- extend typeEnv name (ftvType ty |> Set.toList, ty))
        | _ -> ()

let extendTermMany names v =
    if not <| List.isEmpty names then
        match names, v with
        | [name], v ->
            termEnv <- extend termEnv name v
        | names, VTuple args when List.length args = List.length names ->
            List.zip names args
            |> List.iter (fun (name, ty) ->
                termEnv <- extend termEnv name ty)
        | _ -> ()

while true do
    printf "> "
    let input = System.Console.ReadLine()
    //let input = System.IO.File.ReadAllText "examples/bug0.bonk"
    let ast = parseRepl input
    match ast with
    | Success (names, expr) -> 
        let typed, i = inferProgramRepl typeEnv freshCount expr // TODO: KindEnv
        printfn "%A" (Result.map prettyType typed)
        freshCount <- i
        let prettyName = String.concat ", " names
        match typed with
        | Ok ty ->
            let res = eval termEnv expr
            extendTypeMany names ty
            let typ = (ty |> renameFresh |> prettyType)
            match res with
            | Some res -> 
                if not <| List.isEmpty names then
                    extendTermMany names res
                    printColor <| sprintf "$w%s : $b%s $w= $g%s" prettyName typ (prettyValue res) 
                else
                    printColor <| sprintf "$wit : $b%s $w= $g%s" typ (prettyValue res)
            | None ->
                printfn "Evaluation error"
        | Error err -> printfn "Typing error: %s" err
    | FailureWith err -> printfn "Parsing error: %A" err
    | CompoundFailure err -> printfn "Parsing error: %A" err
    | Failure -> printfn "Parsing error: Unknown."