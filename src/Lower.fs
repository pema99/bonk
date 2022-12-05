module Lower

open Repr
open Inference
open Monad
open Pretty

// TODO: Maybe don't use a list inside the templates. Just reference the class metadata by name.
type AbstractValue =
    | AVType of QualType
    | AVPartialTemplate of string * int * TypedExpr list // name, arity, overloads
    | AVPartialApplied of string * int * TypedExpr list * int Set * QualType list // name, arity, ids, already applied
    | AVTuple of AbstractValue list
    | AVUnionCase of string * AbstractValue

let combinePartials a b =
    match a, b with
    | AVPartialApplied (n1, a1, o1, ids1, t1), AVPartialApplied (n2, a2, o2, ids2, t2) ->
        if List.length t1 > List.length t2 then // TODO: Check equality
            AVPartialApplied (n1, a1, o1, Set.union ids1 ids2, t1)
        else
            AVPartialApplied (n2, a2, o2, Set.union ids1 ids2, t2)
    | _, AVPartialApplied (n, a, o, ids, t) | AVPartialApplied (n, a, o,ids, t), _ ->
        AVPartialApplied (n, a, o, ids, t)
    | a, _ ->
        a // TODO: Check equality

type AbstractTermEnv = Map<string, AbstractValue>
type ResolvedOverloads = Map<int, string>

type LowerM<'t> = ReaderStateM<AbstractTermEnv, ResolvedOverloads * int, 't>
let lower = state
let getAbtractTermEnv = fun (ate, s) -> Ok ate, (ate, s)
let setAbtractTermEnv env = fun (ate, s) -> Ok (), (env, s)
let freshId = fun (ate, (overloads, id)) -> Ok id, (ate, (overloads, id + 1))

let zEncode: string -> string = 
    String.collect (function
        | '(' -> "zlp"
        | ')' -> "zrp"
        | '*' -> "zst"
        | 'z' -> "zz"
        | ''' -> "zq"
        | '<' -> "zl"
        | '>' -> "zg"
        | '_' -> "zu"
        | ' ' -> "zs"
        | ',' -> "zc"
        | '-' -> "zm"
        | '=' -> "ze"
        | '.' -> "zd"
        | c -> string c)

let zDecode: string -> string =
    let rec loop acc = function
        | 'z' :: 'l' :: 'p' :: rest -> loop ('(' :: acc) rest
        | 'z' :: 'r' :: 'p' :: rest -> loop (')' :: acc) rest
        | 'z' :: 's' :: 't' :: rest -> loop ('*' :: acc) rest
        | 'z' :: 'z' :: rest -> loop ('z' :: acc) rest
        | 'z' :: 'q' :: rest -> loop ('\'' :: acc) rest
        | 'z' :: 'l' :: rest -> loop ('<' :: acc) rest
        | 'z' :: 'g' :: rest -> loop ('>' :: acc) rest
        | 'z' :: 'u' :: rest -> loop ('_' :: acc) rest
        | 'z' :: 's' :: rest -> loop (' ' :: acc) rest
        | 'z' :: 'c' :: rest -> loop (',' :: acc) rest
        | 'z' :: 'm' :: rest -> loop ('-' :: acc) rest
        | 'z' :: 'e' :: rest -> loop ('=' :: acc) rest
        | 'z' :: 'd' :: rest -> loop ('.' :: acc) rest
        | c :: rest -> loop (c :: acc) rest
        | [] -> List.rev acc
    Seq.toList >> loop [] >> List.toArray >> System.String

let mangleOverload (func: string) (ts: QualType) : string =
    ts
    |> renameFreshQualType
    |> prettyQualType
    |> sprintf "%s_%s" func
    |> zEncode
    |> sprintf "_%s" // Add underscore for reserved name

let monomorphPrefix = "_monomorph"
let getMonomorphizedName id : string =
    monomorphPrefix + string id

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

let resolveOverload (overloads: TypedExpr list) (args: QualType list) : TypedExpr option =
    match List.tryFind (fun ex -> candidate ex args) overloads with
    | Some goal -> Some goal
    | None -> None

let rec calcArity (ex: TypedExpr) : int =
    match ex with
    | TELam (ty, x, rest) -> 1 + calcArity rest
    | _ -> 0

let rec matchPattern tenv pat (v: AbstractValue) =
    match pat, v with
    | PName a, v ->
        [a, v]
    | PConstant a, v ->
        []
    | PTuple pats, AVTuple vs ->
        let vs = List.map (fun (pat, va) -> matchPattern tenv pat va) (List.zip pats vs)
        vs |> List.concat
    | PUnion (case, pat), AVUnionCase (s, v) ->
        if case = s then matchPattern tenv pat v
        else []
    | _ -> []

and evalPattern (tenv: AbstractTermEnv) pat v =
    match matchPattern tenv pat v with
    | [] -> tenv
    | nv ->
        List.fold (fun env (name, va) -> extend env name va) tenv nv

and gatherOverloadsExpr (e: TypedExpr) : LowerM<TypedExpr * AbstractValue> = lower {
    match e with
    | TELit (qt, _) ->
        return e, AVType qt
    | TEOp (qt, l, op, r) ->
        let! e1, v1 = gatherOverloadsExpr l
        let! e2, v2 = gatherOverloadsExpr r
        return TEOp (qt, e1, op, e2), combinePartials v1 v2
    | TEVar (qt, a) ->
        let! tenv = getAbtractTermEnv
        match lookup tenv a with
        | Some (AVPartialTemplate (name, arity, overloads)) ->
            let! id = freshId
            return TEVar (qt, getMonomorphizedName id), AVPartialApplied (name, arity, overloads, Set.singleton id, [])
        | Some v -> return e, v
        | _ -> return e, AVType qt
    | TEApp (qt, f, x) ->
        let! clos, closval = gatherOverloadsExpr f
        let! arg, argval = gatherOverloadsExpr x
        match closval with
        | AVPartialApplied (name, arity, overloads, ids, args) ->
            let applied = (getExprType x) :: args
            if arity = List.length applied then
                let! (a, (resolved, b)) = get
                match resolveOverload overloads applied with
                | Some overload ->
                    let mangled =
                        overload
                        |> getExprType
                        |> mangleOverload name 
                    let resolved = Set.fold (fun acc id -> extend acc id mangled) resolved ids
                    do! set (a, (resolved, b))
                | _ -> () // TODO: Handle error!
            return TEApp (qt, clos, arg), AVPartialApplied (name, arity, overloads, ids, applied)
        | _ ->
            return TEApp (qt, clos, arg), AVType qt
    | TELam (qt, x, t) ->
        let! body, bodyval = gatherOverloadsExpr t
        return TELam (qt, x, body), AVType qt
    | TELet (qt, x, v, t) ->
        let! value, valueval = gatherOverloadsExpr v
        let! body, bodyval = local (fun tenv -> evalPattern tenv x valueval) (gatherOverloadsExpr t)
        return TELet (qt, x, value, body), bodyval
    | TEGroup (qt, bs, rest) ->
        let! bss =
            mapM (fun (x, v) -> lower {
                let! value, valueval = gatherOverloadsExpr v
                return x, value
            }) bs
        let! rest, restval = gatherOverloadsExpr rest
        return TEGroup (qt, bss, rest), restval
    | TEIf (qt, c, tr, fl) ->
        let! cond, condval = gatherOverloadsExpr c
        let! trueb, truebval = gatherOverloadsExpr tr
        let! falseb, falsebval = gatherOverloadsExpr fl
        return TEIf (qt, cond, trueb, falseb), combinePartials truebval falsebval
    | TETuple (qt, es) ->
        let! res = mapM gatherOverloadsExpr es
        let es, esvals = List.unzip res
        return TETuple (qt, es), AVTuple esvals
    | TEMatch (qt, e, xs) ->
        let! e, eval = gatherOverloadsExpr e
        let! xss =
            mapM (fun (pat, body) -> lower {
                let! value = gatherOverloadsExpr body
                return pat, value 
            }) xs
        let pats, rest = List.unzip xss
        let rest, restvals = List.unzip rest
        let restvals =
            if List.length restvals = 0 then
                AVType qt
            else
                List.fold combinePartials (List.head restvals) restvals
        return TEMatch (qt, e, List.zip pats rest), restvals 
    | TERaw (qt, body) ->
        return e, AVType qt
    }

let gatherOverloadsDecl (decl: TypedDecl) : LowerM<TypedDecl> = lower {
    match decl with
    | TDExpr expr -> 
        let! expr, _ = gatherOverloadsExpr expr
        return TDExpr expr
    | TDLet (pat, expr) ->
        let! e, v = gatherOverloadsExpr expr
        let! tenv = getAbtractTermEnv
        let bindings = matchPattern tenv pat v
        let tenv = extendEnv tenv bindings
        do! setAbtractTermEnv tenv
        return TDLet (pat, e)
    | TDGroup (es) -> // TODO Bindings
        let! exprs =
            mapM (fun (a, b) -> lower {
                let! b, _ = gatherOverloadsExpr b 
                return a, b
            }) es
        return TDGroup exprs
    | TDUnion (name, tvs, cases) ->
        return TDUnion (name, tvs, cases)
    | TDClass (blankets, pred, impls) ->
        return TDClass (blankets, pred, impls) // TODO: Checking?
    | TDMember (blankets, pred, impls) ->
        let addMember (s, e) = lower {
            let! tenv = getAbtractTermEnv
            match lookup tenv s with
            | Some (AVPartialTemplate (name, arity, overloads)) ->
                let tenv = extend tenv s (AVPartialTemplate (name, arity, e :: overloads))
                do! setAbtractTermEnv tenv
            | _ ->
                let tenv = extend tenv s (AVPartialTemplate (s, calcArity e, [e]))
                do! setAbtractTermEnv tenv
        }
        do! mapM_ addMember impls
        return TDMember (blankets, pred, impls)
    }

// Map over typed expr
let rec mapTypedExpr fe ex : TypedExpr =
    match ex with
    | TELit (pt, v)           -> fe <| TELit (pt, v)
    | TEVar (pt, a)           -> fe <| TEVar (pt, a)
    | TEApp (pt, f, x)        -> fe <| TEApp (pt, mapTypedExpr fe f, mapTypedExpr fe x) 
    | TELam (pt, x, e)        -> fe <| TELam (pt, x, mapTypedExpr fe e)
    | TELet (pt, x, e1, e2)   -> fe <| TELet (pt, x, mapTypedExpr fe e1, mapTypedExpr fe e2)
    | TEIf (pt, cond, tr, fl) -> fe <| TEIf (pt, mapTypedExpr fe cond, mapTypedExpr fe tr, mapTypedExpr fe fl)
    | TEOp (pt, l, op, r)     -> fe <| TEOp (pt, mapTypedExpr fe l, op, mapTypedExpr fe r)
    | TETuple (pt, es)        -> fe <| TETuple (pt, List.map (mapTypedExpr fe) es)
    | TEMatch (pt, e, bs)     -> fe <| TEMatch (pt, mapTypedExpr fe e, List.map (fun (a, b) -> a, mapTypedExpr fe b) bs)
    | TEGroup (pt, a, b)      -> fe <| TEGroup (pt, List.map (fun (a, b) -> a, mapTypedExpr fe b) a, mapTypedExpr fe b)
    | TERaw (pt, body)        -> fe <| TERaw (pt, body)

// Map over typed decl
let mapTypedDecl fe fd decl = 
    match decl with
    | TDExpr expr                      -> fd <| TDExpr (mapTypedExpr fe expr)
    | TDLet (pat, expr)                -> fd <| TDLet (pat, mapTypedExpr fe expr)
    | TDGroup (es)                     -> fd <| TDGroup (List.map (fun (a, b) -> a, mapTypedExpr fe b) es)
    | TDUnion (name, tvs, cases)       -> fd <| TDUnion (name, tvs, cases)
    | TDClass (blankets, pred, impls)  -> fd <| TDClass (blankets, pred, impls)
    | TDMember (blankets, pred, impls) -> fd <| TDMember (blankets, pred, impls)

let monomorphizeDecls (tenv: AbstractTermEnv) (decls: TypedDecl list) : TypedDecl list =
    let res, (_, (overloads, _)) = mapM gatherOverloadsDecl decls (Map.empty, (Map.empty, 0))
    match res with
    | Ok mdecls ->
        mdecls
        |> List.map (mapTypedDecl (fun ex ->
            match ex with
            | TEVar (pt, name) when name.StartsWith(monomorphPrefix) -> // TODO: Unsafe
                let id = int <| name.Substring(monomorphPrefix.Length)
                match lookup overloads id with
                | Some mangled -> TEVar (pt, mangled)
                | _ -> ex // TODO: This is the case where a monomorphable type is ambiguous, should report it
            | _ -> ex
            ) id)
    | _ -> decls