module Repl

open Repr
open ReprUtil
open Inference
open Pretty
open Parse
open Prelude
open Semantics
open Lower
open Monad

// Evaluation
let rec buildApp (f: TypedExpr) (args: TypedExpr list): TypedExpr =
    match args with
    | h :: t -> mkFakeExpr (EApp (buildApp f t, h))
    | [] -> f

let rec matchPattern tenv pat v =
    match pat, v with
    | PName a, v ->
        Some [a, v]
    | PConstant a, v ->
        if (eval tenv (mkFakeExpr <| ELit a)) = Some v then Some []
        else None
    | PTuple pats, VTuple vs ->
        let vs = List.map (fun (pat, va) -> matchPattern tenv pat va) (List.zip pats vs)
        if List.forall (Option.isSome) vs then List.choose id vs |> List.concat |> Some
        else None
    | PUnion (case, pat), VUnionCase (s, v) ->
        if case = s then
            match pat, v with
            | Some pat, Some v -> matchPattern tenv pat v
            | None, None -> Some []
            | _ -> None
        else None
    | _ -> None

and evalPattern (tenv: TermEnv) pat v =
    match matchPattern tenv pat v with
    | Some nv ->
        List.fold (fun env (name, va) -> extend env name va) tenv nv
        |> Some
    | None -> None

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
    | VInt l, Modulo, VInt r -> Some <| VInt (l % r)

    | VChar l, Plus, VChar r -> Some <| VChar (l + r)
    | VChar l, Equal, VChar r -> Some <| VBool (l = r)
    | VChar l, NotEq, VChar r -> Some <| VBool (l <> r)
    | VChar l, GreaterEq, VChar r -> Some <| VBool (l >= r)
    | VChar l, LessEq, VChar r -> Some <| VBool (l <= r)
    | VChar l, Greater, VChar r -> Some <| VBool (l > r)
    | VChar l, Less, VChar r -> Some <| VBool (l < r)

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
    | VFloat l, Modulo, VFloat r -> Some <| VFloat (l % r)

    | VString l, Plus, VString r -> Some <| VString (l + r)
    | VString l, Equal, VString r -> Some <| VBool (l = r)
    | VString l, NotEq, VString r -> Some <| VBool (l <> r)
    | VString l, GreaterEq, VString r -> Some <| VBool (l.Length >= r.Length)
    | VString l, LessEq, VString r -> Some <| VBool (l.Length <= r.Length)
    | VString l, Greater, VString r -> Some <| VBool (l.Length > r.Length)
    | VString l, Less, VString r -> Some <| VBool (l.Length < r.Length)
    | VBool l, BoolAnd, VBool r -> Some <| VBool (l && r)
    | VBool l, BoolOr, VBool r -> Some <| VBool (l || r)
    
    | _ -> None

and eval tenv (e: TypedExpr) =
    match e.kind with
    | ELit (LUnit) -> Some VUnit
    | ELit (LInt v) -> Some (VInt v)
    | ELit (LBool v) -> Some (VBool v)
    | ELit (LFloat v) -> Some (VFloat v)
    | ELit (LString v) -> Some (VString v)
    | ELit (LChar v) -> Some (VChar v)
    | EOp (l, op, r) ->
        let v1 = eval tenv l
        let v2 = eval tenv r
        match v1, v2 with
        | Some v1, Some v2 -> binop v1 op v2
        | _ -> None
    | EVar (a) -> lookup tenv a
    | EApp (f, x) ->
        let clos = eval tenv f
        let arg = eval tenv x
        match clos, arg with
        | Some (VUnionCtor a), Some v ->
            Some (VUnionCase (a, Some v))
        | Some (VClosure (selfs, a, body, env)), Some v ->
            let env = List.fold (fun acc self ->
                match lookup tenv self with
                | Some v -> extend acc self v
                | _ -> acc) env selfs
            Option.bind (fun nenv -> eval nenv body) (evalPattern env a v)
        | Some (VIntrinsic (name, args)), Some v ->
            let applied = v :: args
            match lookup funImpls name with
            | Some (impl, arity) ->
                if arity = List.length applied then impl (List.rev applied)
                else Some (VIntrinsic (name, applied))
            | None -> None
        | Some (VOverload (lst, arity, args)), Some _ ->
            let applied = x :: args
            if arity = List.length applied then
                let typs = List.map getExprType (List.rev applied)
                let goal = resolveOverload lst typs
                Option.bind (fun goal -> eval tenv (buildApp goal applied)) goal
            else
                Some (VOverload (lst, arity, applied))
        | _ -> None
    | ELam (x, t) -> Some (VClosure ([], x, t, tenv))
    | ELet (x, v, t) ->
        match eval tenv v with
        | Some ve ->
            Option.bind (fun nenv -> eval nenv t) (evalPattern tenv x ve)
        | _ -> None
    | EGroup (bs, rest) ->
        let bootstrap selfs v =
            match v with
            | VClosure (_, x, t, env) ->
                VClosure (List.map fst selfs, x, t, env)
            | _ -> v
        let evals = List.map (fun (name, body) -> name, eval tenv body) bs
        if List.exists (snd >> Option.isNone) evals then None
        else
            evals
            |> List.map (fun (name, body) -> name, Option.get body)
            |> fun selfs -> List.map (fun (name, body) -> name, bootstrap selfs body) selfs
            |> List.fold (fun acc (name, body) -> extend acc name body) tenv
            |> fun nenv -> eval nenv rest
    | EIf (c, tr, fl) ->
        match eval tenv c with
        | Some (VBool v) ->
            if v 
            then eval tenv tr
            else eval tenv fl 
        | _ -> None
    | ETuple (es) ->
        let ev = List.map (eval tenv) es
        let ev = List.choose id ev
        if List.length es = List.length ev then Some (VTuple ev)
        else None
    | EMatch (e, xs) ->
        match eval tenv e with
        | Some ev ->
            xs
            |> List.map (fun (pat, res) -> Option.map (fun a -> a, res) (evalPattern tenv pat ev))
            |> List.tryPick id
            |> Option.bind (fun (env, hit) -> eval env hit)
        | _ -> None
    | ERaw (_, _) ->
        None

// Repl start
type InferState = TypeEnv * UserEnv * ClassEnv * int
type CheckState = (Set<string> * Set<string> * Set<string>)
type ReplM<'t> = StateM<InferState * CheckState * TermEnv, 't, ErrorInfo>
let repl = state
let getTermEnv : ReplM<TermEnv> = (fun (_,_,a) -> a) <!> get
let setTermEnv x : ReplM<unit> = modify (fun (s, b, _) -> (s, b, x))
let setFreshCount x : ReplM<unit> = modify (fun ((a,b,c,_),d,e) -> ((a,b,c,x),d,e))

let applyEnvUpdate (up: EnvUpdate) (check: CheckState) : ReplM<unit> = repl {
    let! ((typeEnv, userEnv, classEnv, freshCount), _, termEnv) = get
    let (typeUp, userUp, classUp, implUp) = up
    let typeEnv = extendEnv typeEnv typeUp
    let userEnv = extendEnv userEnv userUp
    let classEnv = extendEnv classEnv classUp
    let classEnv = List.fold addClassInstance classEnv implUp
    do! set ((typeEnv, userEnv, classEnv, freshCount), check, termEnv)
    }

// Returns state of checking, just for the REPL
let runColorMRepl (checkState: CheckState) (m: ColorM<_>) =
    let (res, state) = runStateM m checkState
    res |> Result.map (fun a -> a, state)

let checkProgramRepl (env: UserEnv, checkState: CheckState, decls: TypedDecl list) =
    decls
    |> (checkMatches env >> runCheckM)
    |> Result.bind (checkPurity >> runColorMRepl checkState)

let replError (from: Loc) (err: string) =
    let (line, col) = from
    if from = (0, 0) then
        printfn "Error: %s" err
    else
        printfn "Error at line %i, column %i: %s" line col err

let runInfer (decl: UntypedDecl) : ReplM<EnvUpdate * TypedDecl option> = repl {
    let! ((typeEnv, userEnv, classEnv, freshCount), checkState, _) = get
    let res, ((_,uenv,_,_), (_, i)) = runStateM (inferDeclImmediate decl) ((typeEnv, userEnv, classEnv, dummySpan), (Map.empty, freshCount))
    do! setFreshCount i
    match res with
    | Ok (update, tdecl) ->
        let tdecl = checkProgramRepl (uenv, checkState, [tdecl]) |> Result.map (fun (res, state) -> List.head res, state)
        match tdecl with
        | Ok (tdecl, checkState) ->
            do! applyEnvUpdate update checkState
            return update, Some tdecl
        | Error ({span = (from,_); msg = err }) ->
            replError from err
            return ([], [], [], []), None
    | Error ({span = (from,_); msg = err }) ->
        replError from err
        return ([], [], [], []), None
    }

let checkType (name: string) : ReplM<string option> = repl {
    let! ((typeEnv, _, _, _), _, _) = get
    match lookup typeEnv name with
    | Some (_, typ) -> return Some (typ |> prettyQualType)
    | None -> return None
    }

let rec extendTermEnv bindings = repl {
    let! env = getTermEnv
    let env = List.fold (fun acc (n, v) -> extend acc n v) env bindings
    do! setTermEnv env
    }

let rec handleDecl silent decl = repl {
    let! (_, _, _, _), tdecl = runInfer decl
    let! tenv = getTermEnv
    let handleBindings vs = repl {
        do! extendTermEnv vs
        do! mapM_ (fun (name, res) -> repl {
            match! checkType name with
            | Some typ when not silent ->
                printColor <| sprintf "$w%s : $b%s $w= $g%s" name typ (prettyValue res)
            | _ -> ()
            }) vs
        }
    match Option.map (fun x -> x.kind) tdecl with
    | Some (DExpr expr) ->
        match! checkType "it" with
        | Some typ when not silent ->
            let opt = 
                eval tenv expr
                |> Option.map (fun res -> printColor <| sprintf "$wit : $b%s $w= $g%s" typ (prettyValue res))
            if Option.isNone opt then
                printfn "Evaluation error"
        | _ -> ()
    | Some (DLet (pat, expr)) ->
        let vs = eval tenv expr |> Option.bind (matchPattern tenv pat)
        match vs with
        | Some vs -> do! handleBindings vs
        | None -> printfn "Evaluation failure"
    | Some (DGroup (es)) ->
        let vs = List.map (fun (name, _) ->
            eval tenv (mkFakeExpr (EGroup (es, mkFakeExpr (EVar name))))
            |> Option.bind (matchPattern tenv (PName name))) es
        if List.exists Option.isNone vs then printfn "Evaluation failure"
        else do! handleBindings (List.choose id vs |> List.concat)
    | Some (DUnion (_, _, cases)) ->
        do! extendTermEnv (
            List.map (fun (s, v) ->
                match v with
                | Some _ -> s, VUnionCtor s
                | None -> s, VUnionCase (s, None)) cases)
        let names, _ = List.unzip cases
        do! mapM_ (fun case -> repl {
                let decl = {
                    kind = DLet (PName case, mkExpr (EVar case) dummySpan)
                    span = dummySpan
                    qualifiers = Set.empty
                    data = ()
                }
                return! handleDecl silent decl 
                }) names
    | Some (DMember (pred, impls)) ->
        do! mapM_ (fun (s, e) -> repl {
            let! env = getTermEnv
            match lookup env s with
            | Some (VOverload (lst, arity, v)) -> do! extendTermEnv [s, VOverload (e :: lst, arity, v)]
            | None -> do! extendTermEnv [s, VOverload ([e], calcArityType (snd e.data), [])]
            | _ -> ()
            }) impls
    | _ -> ()// TODO: Typeclasses
    }

let runExpr input = repl {
    let ast = parseDecl input
    match ast with
    | Ok (decl) -> do! handleDecl false decl
    | Error (span, msg) -> replError (fst span) msg
}

let rec readUntilSemicolon (str: string) =
    if str.Trim().EndsWith(";") then
        str
    else
        printf "- "
        let ns = System.Console.ReadLine()
        str + "\n" + readUntilSemicolon ns

let loadLibrary silent input = repl {
    let ast = parseProgram input
    match ast with
    | Ok decls -> do! mapM_ (handleDecl silent) decls
    | Error (span, err) -> replError (fst span) err
}

let runRepl stdlib : ReplM<unit> = repl {
    if stdlib then
        do! loadLibrary true stdLib
    printfn "Welcome to the Bonk REPL, type ':h' for help."
    while true do
        printf "> "
        let input = System.Console.ReadLine()
        let trimmed = input.Trim()
        if trimmed.StartsWith(":") then
            let ops = trimmed.Split(" ")
            match trimmed.[1] with
            | 't' when ops.Length > 1 -> 
                match! checkType (ops.[1]) with
                | Some (ty) -> printColor <| sprintf "$w%s : $b%s" (ops.[1]) ty
                | _ -> printfn "Invalid identifier!"
            | 'f' when ops.Length > 1 ->
                do! loadLibrary false (System.IO.File.ReadAllText ops.[1])
            | 's' ->
                let! ((typeEnv, _, _, _), _, termEnv) = get
                let filter = if ops.Length > 1 then ops.[1] else ""
                let names = Map.toList typeEnv |> List.map fst
                names
                |> Seq.filter (fun name -> name.Contains filter)
                |> Seq.map (fun name -> name, lookup typeEnv name, lookup termEnv name)
                |> Seq.iter (fun (name, ty, te) ->
                    match ty, te with
                    | Some (_, ty), Some te ->
                        printColor <| sprintf "$w%s : $b%s $w= $g%s" name (prettyQualType ty) (prettyValue te)
                    | _ -> ())
            | 'q' ->
                System.Environment.Exit 0
            | 'h' ->
                printfn "Type an expression followed by a semicolon to evaluate it."
                printfn "You can use the following commands:"
                printfn ":f <path>            Load code from a path and evaluate it."
                printfn ":t <identifier>      Print the type of a bound variable."
                printfn ":s <filter>          Show all bindings optionally filtered to a string."
                printfn ":h                   Print this help message."
                printfn ":q                   Exit the REPL."
            | _ ->
                printfn "Invalid command. Type ':h' for help."
        else
            do! runExpr (readUntilSemicolon input)
}

let runReplAction prelude (action: ReplM<'t>) =
    let funSchemes = if prelude then funSchemes else Map.empty
    runStateM action (
        (funSchemes, Map.empty, classes, 0),                // Infer state
        (funImpures, funImpureExceptions, Set.empty),       // Check state
        Map.map (fun k _ -> VIntrinsic (k, [])) funSchemes) // Term state
    |> fst
    
let startRepl builtins stdlib =
    runReplAction builtins (runRepl stdlib)
    |> ignore