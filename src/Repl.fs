module Repl

open Repr
open Inference
open Monad
open Pretty
open Combinator
open Parse

// Repr
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

// Evaluation
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

// Repl start
type ReplM<'t> = StateM<TypeEnv * TermEnv * UserEnv * int, 't>
let repl = state
let setEnv f = repl {
    let! a = get
    do! set (f a)
}
let setTypeEnv env  = setEnv (fun (_, b, c, d) -> (env, b, c, d)) 
let setTermEnv env  = setEnv (fun (a, _, c, d) -> (a, env, c, d)) 
let setUserEnv env  = setEnv (fun (a, b, _, d) -> (a, b, env, d)) 
let setFreshCount i = setEnv (fun (a, b, c, _) -> (a, b, c, i)) 

let rec extendTypeEnv pat typ = repl {
    let! (typeEnv, _, _, _) = get
    match pat, typ with
    | PName a, typ ->
        do! setTypeEnv (extend typeEnv a (ftvType typ |> Set.toList, typ))
        return true
    | PTuple pats, TCtor (KProduct, typs) ->
        let! _ = mapM (fun (pat, va) -> extendTypeEnv pat va) (List.zip pats typs)
        return true
    | _ ->
        return false
}

let rec extendTermEnv pat v = repl {
    let! (typeEnv, termEnv, userEnv, freshCount) = get
    match matchPattern termEnv pat v with
    | Some nenv ->
        do! setTermEnv nenv
        return true
    | _ ->
        return false
}

let handleExpr expr = repl {
    let! (typeEnv, termEnv, userEnv, freshCount) = get
    let typed, i = inferProgramRepl typeEnv freshCount expr
    do! setFreshCount i
    match typed with
    | Ok typ ->
        let res = eval termEnv expr
        match res with
        | Some res -> return Ok (typ, res)
        | None -> return Error "Evaluation error"
    | Error err -> return Error err
}

let rec handleDecl decl = repl {
    match decl with
    | DExpr expr ->
        match! handleExpr expr with
        | Ok (typ, res) ->
            let typ = typ |> renameFresh |> prettyType
            printColor <| sprintf "$wit : $b%s $w= $g%s" typ (prettyValue res)
        | Error err -> printfn "%s" err
    | DLet (pat, expr) ->
        let prettyName = prettyPattern pat
        match! handleExpr expr with
        | Ok (typ, res) ->
            let ptyp = typ |> renameFresh |> prettyType
            let! s1 = extendTypeEnv pat typ
            let! s2 = extendTermEnv pat res
            if s1 && s2 then
                printColor <| sprintf "$w%s : $b%s $w= $g%s" prettyName ptyp (prettyValue res) 
            else
                printfn "Evaluation error: Failed to match pattern '%s' with type '%s'" (prettyPattern pat) ptyp
        | Error err -> printfn "%s" err
    | DUnion (name, tvs, cases) ->
        let names, typs = List.unzip cases
        let! _ =
            mapM (fun case -> repl {
                let decl = DLet (PName case, EUnion (name, tvs, cases, EVar case))
                return! handleDecl decl }) names
        ()
}

let runExpr input = repl {
    let ast = parseRepl input
    match ast with
    | Success (decl) -> do! handleDecl decl
    | FailureWith err -> printfn "Parsing error: %A" err
    | CompoundFailure err -> printfn "Parsing error: %A" err
    | Failure -> printfn "Parsing error: Unknown."
}

let runRepl : ReplM<unit> = repl {
    printfn "Welcome to the Bonk REPL, type ':h' for help."
    while true do
        printf "> "
        let input = System.Console.ReadLine()
        let trimmed = input.Trim()
        if trimmed.StartsWith(":") then
            let ops = trimmed.Split(" ")
            match trimmed.[1] with
            | 't' when ops.Length > 1 -> 
                let! (typeEnv, _, _, _) = get
                match lookup typeEnv (ops.[1]) with
                | Some (_, ty) -> printColor <| sprintf "$w%s : $b%s" (ops.[1]) (prettyType ty)
                | _ -> printfn "Invalid identifier!"
            | 'f' when ops.Length > 1 ->
                do! runExpr (System.IO.File.ReadAllText ops.[1])
            | 'q' ->
                System.Environment.Exit 0
            | 'h' ->
                printfn "Type an expression to evaluate it."
                printfn "You can use the following commands:"
                printfn ":t <identifier>      Print the type of a bound variable."
                printfn ":f <path>            Load code from a path and evaluate it."
                printfn ":h                   Print this help message."
                printfn ":q                   Exit the REPL."
            | _ ->
                printfn "Invalid command. Type ':h' for help."
        else do! runExpr input
}

runRepl (Map.empty, Map.empty, Map.empty, 0)
|> ignore