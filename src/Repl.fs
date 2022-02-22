module Repl

open Repr
open Inference
open Monad
open Pretty
open Combinator
open Parse
open Prelude
open CodeGen

// Evaluation
let rec compatible (l: QualType) (r: QualType) : bool =
    match l, r with
    | l, r when l = r -> // precisely equall types
        true
    | (_, TConst a), (_, TConst b) when a = b -> // same typed constants
        true
    | (qs, TVar a), b | b, (qs, TVar a) ->
        true // TODO!!!
    | (ql, TArrow (lf, lt)), (qr, TArrow (rf, rt)) -> // arrow types, check both sides
        compatible (ql, lf) (qr, rf) && compatible (ql, lt) (qr, rt)
    | (ql, TCtor (lk, ls)), (qr, TCtor (rk, rs)) when lk = rk -> // ctor types, check all pairs
        let qls = List.map (fun a -> ql, a) ls
        let qrs = List.map (fun a -> qr, a) rs
        List.forall (fun (a, b) -> compatible a b) (List.zip qls qrs)
    | _ -> false

let rec candidate (overload: TypedExpr) (args: QualType list) : bool =
    match overload, args with
    | TELam ((qt, TArrow (a, _)), x, rest), h :: t ->
        compatible (qt, a) h && candidate rest t
    | _, [] -> true 
    | _ -> false

let resolveOverload (overloads: (Inst * TypedExpr) list) (args: QualType list) : TypedExpr option =
    match List.tryFind (fun (_, ex) -> candidate ex args) overloads with
    | Some (_, goal) -> Some goal
    | None -> None

let rec calcArity (ex: TypedExpr) : int =
    match ex with
    | TELam (ty, x, rest) -> 1 + calcArity rest
    | _ -> 0

let rec buildApp (f: TypedExpr) (args: TypedExpr list) =
    match args with
    | h :: t -> TEApp (([], tVoid), buildApp f t, h)
    | [] -> f

let rec matchPattern tenv pat v =
    match pat, v with
    | PName a, v ->
        Some [a, v]
    | PConstant a, v ->
        if (eval tenv (TELit (([], tVoid), a))) = Some v then Some []
        else None
    | PTuple pats, VTuple vs ->
        let vs = List.map (fun (pat, va) -> matchPattern tenv pat va) (List.zip pats vs)
        if List.forall (Option.isSome) vs then List.choose id vs |> List.concat |> Some
        else None
    | PUnion (case, pat), VUnionCase (s, v) ->
        if case = s then matchPattern tenv pat v
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
    | VBool l, And, VBool r -> Some <| VBool (l && r)
    | VBool l, Or, VBool r -> Some <| VBool (l || r)
    
    | _ -> None

and eval tenv (e: TypedExpr) =
    match e with
    | TELit (_, LUnit) -> Some VUnit
    | TELit (_, LInt v) -> Some (VInt v)
    | TELit (_, LBool v) -> Some (VBool v)
    | TELit (_, LFloat v) -> Some (VFloat v)
    | TELit (_, LString v) -> Some (VString v)
    | TELit (_, LChar v) -> Some (VChar v)
    | TEOp (_, l, op, r) ->
        let v1 = eval tenv l
        let v2 = eval tenv r
        match v1, v2 with
        | Some v1, Some v2 -> binop v1 op v2
        | _ -> None
    | TEVar (_, a) -> lookup tenv a
    | TEApp (_, f, x) ->
        let clos = eval tenv f
        let arg = eval tenv x
        match clos, arg with
        | Some (VUnionCtor a), Some v ->
            Some (VUnionCase (a, v))
        | Some (VClosure (a, body, env)), Some v ->
            let env = 
                match f with
                | TEVar (_, fn) -> extend env fn (VClosure (a, body, env))
                | _ -> env
            Option.bind (fun nenv -> eval nenv body) (evalPattern env a v )
        | Some (VLazy e), Some v -> // deferred application
            match e.Value with
            | VClosure (a, body, env) ->
                Option.bind (fun nenv -> eval nenv body) (evalPattern env a v)
            | _ -> None
        | Some (VIntrinsic (name, args)), Some v ->
            let applied = v :: args
            match lookup funImpls name with
            | Some (impl, arity) ->
                if arity = List.length applied then impl (List.rev applied)
                else Some (VIntrinsic (name, applied))
            | None -> None
        | Some (VOverload (lst, arity, args)), Some v ->
            let applied = x :: args
            if arity = List.length applied then
                let typs = List.map getExprType applied
                let goal = resolveOverload lst typs
                Option.bind (fun goal -> eval tenv (buildApp goal applied)) goal
            else
                Some (VOverload (lst, arity, applied))
        | _ -> None
    | TELam (_, x, t) -> Some (VClosure (x, t, tenv))
    | TELet (_, x, v, t) ->
        match eval tenv v with
        | Some ve ->
            Option.bind (fun nenv -> eval nenv t) (evalPattern tenv x ve)
        | _ -> None
    | TEIf (_, c, tr, fl) ->
        match eval tenv c with
        | Some (VBool v) ->
            if v 
            then eval tenv tr
            else eval tenv fl 
        | _ -> None
    | TETuple (_, es) ->
        let ev = List.map (eval tenv) es
        let ev = List.choose id ev
        if List.length es = List.length ev then Some (VTuple ev)
        else None
    | TERec (ty, e) ->
        lazy (eval tenv (TEApp (ty, e, (TERec (ty, e)))) |> Option.get) // TODO: Are the types right here?
        |> fun x -> Some (VLazy x)
    | TEMatch (_, e, xs) ->
        match eval tenv e with
        | Some ev ->
            xs
            |> List.map (fun (pat, res) -> Option.map (fun a -> a, res) (evalPattern tenv pat ev))
            |> List.tryPick id
            |> Option.bind (fun (env, hit) -> eval env hit)
        | _ -> None

// Repl start
type InferState = TypeEnv * UserEnv * ClassEnv * int
type ReplM<'t> = StateM<InferState * TermEnv, 't>
let repl = state
let getTermEnv : ReplM<TermEnv> = fmap snd get
let setTermEnv x : ReplM<unit> = fun (s, _) -> (Ok (), (s, x))
let setFreshCount x : ReplM<unit> = fun ((a,b,c,d),e) -> (Ok (), ((a,b,c,x),e))

let extendEnv env up =
    List.fold (fun env (name, v) -> extend env name v) env up

let addClassInstance (cls: ClassEnv) (name: string, inst: Inst) : ClassEnv =
    match lookup cls name with
    | Some (reqs, impls) -> extend cls name (reqs, inst :: impls)
    | None -> cls

let applyEnvUpdate (up: EnvUpdate) : ReplM<unit> = repl {
    let! ((typeEnv, userEnv, classEnv, freshCount), termEnv) = get
    let (typeUp, userUp, classUp, implUp) = up
    let typeEnv = extendEnv typeEnv typeUp
    let userEnv = extendEnv userEnv userUp
    let classEnv = extendEnv classEnv classUp
    let classEnv = List.fold addClassInstance classEnv implUp
    do! set ((typeEnv, userEnv, classEnv, freshCount), termEnv)
    }

let runInfer (decl: Decl) : ReplM<EnvUpdate * TypedDecl option> = repl {
    let! ((typeEnv, userEnv, classEnv, freshCount), termEnv) = get
    let res, (_, (_, i)) = inferDecl decl ((typeEnv, userEnv, classEnv), (Map.empty, freshCount))
    do! setFreshCount i
    match res with
    | Ok (update, tdecl) ->
        do! applyEnvUpdate update
        return update, Some tdecl
    | Error err ->
        printfn "Type error: %s" err
        return ([], [], [], []), None
    }

let checkType (name: string) : ReplM<string option> = repl {
    let! ((typeEnv, _, _, _), _) = get
    match lookup typeEnv name with
    | Some (_, typ) -> return Some (typ |> renameFreshQualType |> prettyQualType)
    | None -> return None
    }

let rec extendTermEnv bindings = repl {
    let! env = getTermEnv
    let env = List.fold (fun acc (n, v) -> extend acc n v) env bindings
    do! setTermEnv env
    }

let rec handleDecl silent decl = repl {
    let! (varBindings, _, _, _), tdecl = runInfer decl
    let! tenv = getTermEnv
    match tdecl with
    | Some (TDExpr expr) ->
        match! checkType "it" with
        | Some typ when not silent ->
            let opt = 
                eval tenv expr
                |> Option.map (fun res -> printColor <| sprintf "$wit : $b%s $w= $g%s" typ (prettyValue res))
            if Option.isNone opt then
                printfn "Evaluation error"
        | _ -> ()
    | Some (TDLet (pat, expr)) ->
        let vs = eval tenv expr |> Option.bind (matchPattern tenv pat)
        match vs with
        | Some vs ->
            do! extendTermEnv vs
            do! mapM_ (fun (name, res) -> repl {
                match! checkType name with
                | Some typ when not silent ->
                    printColor <| sprintf "$w%s : $b%s $w= $g%s" name typ (prettyValue res)
                | _ -> ()
                }) vs
        | None ->
            printfn "Evaluation failure"//TODO: Print
            //printfn "Evaluation error: Failed to match pattern '%s' with type '%s'" prettyName ptyp
    | Some (TDUnion (name, tvs, cases)) ->
        let ctors = List.map fst cases
        do! extendTermEnv (List.map (fun s -> s, (VUnionCtor s)) ctors)
        let names, typs = List.unzip cases
        do! mapM_ (fun case -> repl {
                let decl = DLet (PName case, EVar case)
                return! handleDecl silent decl 
                }) names
    | Some (TDMember (blankets, pred, impls)) ->
        let inst = blankets, pred
        do! mapM_ (fun (s, e) -> repl {
            let! env = getTermEnv
            match lookup env s with
            | Some (VOverload (lst, arity, v)) -> do! extendTermEnv [s, VOverload ((inst, e) :: lst, arity, v)]
            | None -> do! extendTermEnv [s, VOverload ([inst, e], calcArity e, [])]
            | _ -> ()
            }) impls
    | _ -> ()// TODO: Typeclasses
    }

let runExpr input = repl {
    let ast = parseDecl input
    //printfn "%A" ast
    match ast with
    | Success (decl) -> do! handleDecl false decl
    | FailureWith err -> printfn "Parsing error: %A" err
    | CompoundFailure err -> printfn "Parsing error: %A" err
    | Failure -> printfn "Parsing error: Unknown."
}

let rec readUntilSemicolon (str: string) =
    if str.Trim().EndsWith(";") then
        str
    else
        printf "- "
        let ns = System.Console.ReadLine()
        str + readUntilSemicolon ns

let loadLibrary silent input = repl {
    let ast = parseProgram input
    match ast with
    | Success decls -> do! mapM_ (handleDecl silent) decls
    | _ -> printfn "Failed to load library."
}

// Attempt to load std lib
let stdLib = 
    use res =
        System.Reflection.Assembly
            .GetExecutingAssembly()
            .GetManifestResourceStream("bonk.lib.prelude.bonk")
    let out = Array.create (int res.Length) (byte 0)
    res.Read(out, 0, int res.Length) |> ignore
    System.Text.Encoding.Default.GetString(out)

let runRepl : ReplM<unit> = repl {
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
                let! ((typeEnv, _, _, _), termEnv) = get
                let filter = if ops.Length > 1 then ops.[1] else ""
                let names = Map.toList typeEnv |> List.map fst
                names
                |> Seq.filter (fun name -> name.Contains filter)
                |> Seq.map (fun name -> name, lookup typeEnv name, lookup termEnv name)
                |> Seq.iter (fun (name, ty, te) ->
                    match ty, te with
                    | Some (_, ty), Some te ->
                        printColor <| sprintf "$w%s : $b%s $w= $g%s" name (prettyQualType (renameFreshQualType ty)) (prettyValue te)
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

let runReplAction prelude action =
    let funSchemes = if prelude then funSchemes else Map.empty
    action ((funSchemes, Map.empty, classes, 0), Map.map (fun k v -> VIntrinsic (k, [])) funSchemes)
    |> fst

let startRepl() =
    runReplAction true runRepl
    |> ignore