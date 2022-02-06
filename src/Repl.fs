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
    | VUnionCtor of string
    | VUnionCase of string * Value
    | VClosure of Pat * Expr * TermEnv
    | VLazy of Value Lazy

and TermEnv = Map<string, Value>

let rec matchPattern tenv pat v =
    match pat, v with
    | PName a, v ->
        Some (extend tenv a v)
    | PConstant a, v ->
        if (eval tenv (ELit a)) = Some v then Some tenv
        else None
    | PTuple pats, VTuple vs ->
        List.fold (fun env (pat, va) -> 
            Option.bind (fun env -> matchPattern env pat va) env)
                (Some tenv) (List.zip pats vs)
    | PUnion (case, pat), VUnionCase (s, v) ->
        if case = s then matchPattern tenv pat v
        else None
    | _ -> None

and binop l op r =
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
    | ELit LUnit -> Some VUnit
    | ELit (LInt v) -> Some (VInt v)
    | ELit (LBool v) -> Some (VBool v)
    | ELit (LFloat v) -> Some (VFloat v)
    | ELit (LString v) -> Some (VString v)
    | EOp (l, op, r) ->
        let v1 = eval tenv l
        let v2 = eval tenv r
        match v1, v2 with
        | Some v1, Some v2 -> binop v1 op v2
        | _ -> None
    | EVar a -> lookup tenv a
    | EApp (f, x) ->
        let clos = eval tenv f
        let arg = eval tenv x
        match clos, arg with
        | Some (VUnionCtor a), Some v ->
            Some (VUnionCase (a, v))
        | Some (VClosure (a, body, env)), Some v ->
            Option.bind (fun nenv -> eval nenv body) (matchPattern env a v )
        | Some (VLazy e), Some v -> // deferred application
            match e.Value with
            | VClosure (a, body, env) ->
                Option.bind (fun nenv -> eval nenv body) (matchPattern env a v )
            | _ -> None
        | _ -> None
    | ELam (x, t) -> Some (VClosure (x, t, tenv))
    | ELet (x, v, t) ->
        match eval tenv v with
        | Some ve ->
            Option.bind (fun nenv -> eval nenv t) (matchPattern tenv x ve)
        | _ -> None
    | EIf (c, tr, fl) ->
        match eval tenv c with
        | Some (VBool v) ->
            if v 
            then eval tenv tr
            else eval tenv fl 
        | _ -> None
    | ETuple es ->
        let ev = List.map (eval tenv) es
        let ev = List.choose id ev
        if List.length es = List.length ev then Some (VTuple ev)
        else None
    | ERec e ->
        lazy (eval tenv (EApp (e, (ERec e))) |> Option.get)
        |> fun x -> Some (VLazy x)
    | EUnion (_, _, cases, body) ->
        let ctors = List.map fst cases
        let nenv = List.fold (fun acc s -> extend acc s (VUnionCtor s)) tenv ctors
        eval nenv body
    | EMatch (e, xs) ->
        match eval tenv e with
        | Some ev ->
            xs
            |> List.map (fun (pat, res) -> Option.map (fun a -> a, res) (matchPattern tenv pat ev))
            |> List.tryPick id
            |> Option.bind (fun (env, hit) -> eval env hit)
        | _ -> None

// Printing
let rec prettyValue v =
    match v with
    | VUnit -> "()"
    | VInt v -> string v
    | VBool v -> string v
    | VFloat v -> string v
    | VString v -> sprintf "%A" v
    | VTuple v -> sprintf "(%s)" <| String.concat ", " (List.map prettyValue v)
    | VUnionCase (n, v) -> sprintf "%s %s" n (prettyValue v)
    | VClosure _ | VUnionCtor _ | VLazy _ -> "Closure"

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
    | Success (names, expr) -> // TODO: general patterns
        let typed, i = inferProgramRepl typeEnv freshCount expr // TODO: KindEnv
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