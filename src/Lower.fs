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

let monomorphizeDecls (decls: TypedDecl list) : TypedDecl list =
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

type ShadowEnv = Map<string, int>
type ShadowM<'t> = ReaderStateM<ShadowEnv, unit, 't>
let shadow = state
let getShadowEnv = fun (ate, s) -> Ok ate, (ate, s)
let setShadowEnv env = fun (ate, s) -> Ok (), (env, s)
let renameShadowed name = shadow {
    let! senv = getShadowEnv
    match lookup senv name with
    | Some v ->
        if v = 0 then return name
        else return sprintf "_%s%i" name v
    | _ -> return name
} 
//let shadowName name = fun (ate, id) -> Ok ("__" + name + string id), (ate,  id + 1)

let rec getNamesInPattern (pat: Pattern) : string list =
    match pat with
    | PName a -> [a]
    | PConstant _ -> []
    | PTuple pats -> pats |> List.collect getNamesInPattern
    | PUnion (_, pat) -> getNamesInPattern pat


let rec renameShadowedVarsInPattern (pat: Pattern) : ShadowM<Pattern> = shadow {
    match pat with
    | PName a ->
        return! fmap PName <| renameShadowed a
    | PConstant _ ->
        return pat
    | PTuple pats ->
        let! pats = mapM renameShadowedVarsInPattern pats
        return PTuple pats
    | PUnion (case, pat) ->
        return! fmap (fun rpat -> PUnion (case, rpat)) <| renameShadowedVarsInPattern pat
}

let shadowNewName (pat: Pattern) : ShadowM<Pattern * (ShadowEnv -> ShadowEnv)> = shadow {
    let! senv = getShadowEnv
    let rec cont names senv =
        match names with
        | [] -> senv
        | name :: rest ->
            let senv = extend senv name (1 + (lookup senv name |> Option.defaultValue (-1)))
            cont rest senv
    let senv = cont (getNamesInPattern pat) senv
    let mapper = fun _ -> senv
    let! pat = local mapper (renameShadowedVarsInPattern pat)
    return pat, mapper
}

let shadowNewString (name: string) : ShadowM<string * (ShadowEnv -> ShadowEnv)> = shadow {
    let! senv = getShadowEnv
    let senv = extend senv name (1 + (lookup senv name |> Option.defaultValue 0))
    let mapper = fun _ -> senv
    let! name = local mapper (renameShadowed name)
    return name, mapper
}

let rec renameShadowedVarsInExpr (e: TypedExpr) : ShadowM<TypedExpr> = shadow {
    match e with
    | TELit (qt, _) ->
        return e
    | TEOp (qt, l, op, r) ->
        let! e1 = renameShadowedVarsInExpr l
        let! e2 = renameShadowedVarsInExpr r
        return TEOp (qt, e1, op, e2)
    | TEVar (qt, a) ->
        let! renamed = renameShadowed a
        return TEVar (qt, renamed)
    | TEApp (qt, f, x) ->
        let! clos = renameShadowedVarsInExpr f
        let! arg = renameShadowedVarsInExpr x
        return TEApp (qt, clos, arg)
    | TELam (qt, x, t) ->
        let! pat, mapper = shadowNewName x
        let! body = local mapper (renameShadowedVarsInExpr t)
        return TELam (qt, pat, body)
    | TELet (qt, x, v, t) ->
        let! pat, mapper = shadowNewName x
        let! value = renameShadowedVarsInExpr v
        let! body = local mapper (renameShadowedVarsInExpr t)
        return TELet (qt, pat, value, body)
    | TEGroup (qt, bs, rest) ->
        let! bss =
            // TODO: Think this should technically be a fold over the mappers. Oh well.
            mapM (fun (x, v) -> lower {
                let! x, mapper = shadowNewString x
                let! expr = local mapper (renameShadowedVarsInExpr v)
                return (x, expr), mapper
            }) bs
        let bsss, mappers = bss |> List.unzip
        let mapper = List.fold (>>) id mappers
        let! rest = local mapper (renameShadowedVarsInExpr rest)
        return TEGroup (qt, bsss, rest)
    | TEIf (qt, c, tr, fl) ->
        let! cond = renameShadowedVarsInExpr c
        let! trueb = renameShadowedVarsInExpr tr
        let! falseb = renameShadowedVarsInExpr fl
        return TEIf (qt, cond, trueb, falseb)
    | TETuple (qt, es) ->
        let! res = mapM renameShadowedVarsInExpr es
        return TETuple (qt, res)
    | TEMatch (qt, e, xs) ->
        let! e = renameShadowedVarsInExpr e
        let! xss =
            // Intentionally don't extract bindings here,
            // since bindings in matches are scoped to the match bodies
            mapM (fun (pat, body) -> lower {
                let! pat, mapper = shadowNewName pat
                let! value = local mapper (renameShadowedVarsInExpr body)
                return pat, value 
            }) xs
        let pats, rest = List.unzip xss
        return TEMatch (qt, e, List.zip pats rest)
    | TERaw (qt, body) ->
        return e
    }

let renamedShadowedVarsInDecl (decl: TypedDecl) : ShadowM<TypedDecl> = shadow {
    match decl with
    | TDExpr expr -> 
        let! expr = renameShadowedVarsInExpr expr
        return TDExpr expr
    | TDLet (pat, expr) ->
        let! e = renameShadowedVarsInExpr expr
        let! pat, mapper = shadowNewName pat
        let! senv = getShadowEnv
        do! setShadowEnv (mapper senv)
        return TDLet (pat, e)
    | TDGroup (es) -> // TODO Bindings
        let! exprs =
            mapM (fun (pat, e) -> lower {
                let! e = renameShadowedVarsInExpr e
                let! pat, mapper = shadowNewName (PName pat)
                let pat = match pat with PName n -> n | _ -> "_failure"
                let! senv = getShadowEnv
                do! setShadowEnv (mapper senv)
                return pat, e
            }) es
        return TDGroup exprs
    | TDUnion (name, tvs, cases) ->
        return TDUnion (name, tvs, cases)
    | TDClass (blankets, pred, impls) ->
        return TDClass (blankets, pred, impls)
    | TDMember (blankets, pred, impls) ->
        let! impls = 
            mapM (fun (name, expr) -> lower {
                let! expr = renameShadowedVarsInExpr expr
                return name, expr
            }) impls
        return TDMember (blankets, pred, impls)
    }

let renamedShadowedVarsInDecls (decls: TypedDecl list) : TypedDecl list =
    let res, _ = mapM renamedShadowedVarsInDecl decls (Map.empty, ())
    match res with
    | Ok mdecls -> mdecls
    | _ -> decls

let lowerDecls = monomorphizeDecls >> renamedShadowedVarsInDecls