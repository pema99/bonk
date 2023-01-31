module Lower

open Repr
open ReprUtil
open Monad
open Pretty

// TODO: Maybe don't use a list inside the templates. Just reference the class metadata by name.
// TODO: Closures
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

type LowerM<'t> = ReaderStateM<AbstractTermEnv, ResolvedOverloads * int, 't, ErrorInfo>
let lower = state
let freshId = modifyR (fun (overloads, id) -> overloads, id + 1) >>. (snd <!> getR)

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
    |> sprintf "$%s" // Add $ for reserved name

let monomorphPrefix = "$monomorph"
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
    | (ql, TCtor (lk, ls)), (qr, TCtor (rk, rs)) when lk = rk -> // ctor types, check all pairs
        let qls = List.map (fun a -> ql, a) ls
        let qrs = List.map (fun a -> qr, a) rs
        List.forall (fun (a, b) -> compatible a b) (List.zip qls qrs)
    | _ -> false

let rec candidate (overload: QualType) (args: QualType list) : bool =
    match overload, args with
    | (ql, TCtor (KArrow, [lf; lt])), h :: t ->
        compatible (ql, lf) h && candidate (ql, lt) t
    | _, [] -> true 
    | _ -> false

let resolveOverload (overloads: TypedExpr list) (args: QualType list) : TypedExpr option =
    match List.tryFind (fun ex -> candidate (getExprType ex) args) overloads with
    | Some goal -> Some goal
    | None -> None

let rec matchPattern tenv pat (v: AbstractValue) =
    match pat, v with
    | PName a, v ->
        [a, v]
    | PConstant _, _ ->
        []
    | PTuple pats, AVTuple vs ->
        let vs = List.map (fun (pat, va) -> matchPattern tenv pat va) (List.zip pats vs)
        vs |> List.concat
    | PUnion (case, pat), AVUnionCase (s, v) ->
        match pat with
        | None -> []
        | Some pat ->
            if case = s then matchPattern tenv pat v
            else []
    | _ -> []

and evalPattern (tenv: AbstractTermEnv) pat v =
    match matchPattern tenv pat v with
    | [] -> tenv
    | nv ->
        List.fold (fun env (name, va) -> extend env name va) tenv nv

and gatherOverloadsExpr (inExpr: TypedExpr) : LowerM<TypedExpr * AbstractValue> = lower {
    match inExpr.kind with
    | ELit (_) ->
        return inExpr, AVType inExpr.data
    | EOp (l, op, r) ->
        let! e1, v1 = gatherOverloadsExpr l
        let! e2, v2 = gatherOverloadsExpr r
        return { inExpr with kind = EOp (e1, op, e2) }, combinePartials v1 v2
    | EVar (a) ->
        let! tenv = ask
        match lookup tenv a with
        | Some (AVPartialTemplate (name, arity, overloads)) ->
            let! id = freshId
            return { inExpr with kind = EVar (getMonomorphizedName id) }, AVPartialApplied (name, arity, overloads, Set.singleton id, [])
        | Some v -> return inExpr, v
        | _ -> return inExpr, AVType inExpr.data
    | EApp (f, x) ->
        let! clos, closval = gatherOverloadsExpr f
        let! arg, _ = gatherOverloadsExpr x
        match closval with
        | AVPartialApplied (name, arity, overloads, ids, args) ->
            let applied = (getExprType x) :: args
            if arity = List.length applied then
                let! (a, (resolved, b)) = get
                match resolveOverload overloads (List.rev applied) with
                | Some overload ->
                    let mangled =
                        overload
                        |> getExprType
                        |> mangleOverload name 
                    let resolved = Set.fold (fun acc id -> extend acc id mangled) resolved ids
                    do! set (a, (resolved, b))
                | _ -> () // TODO: Handle error!
            return { inExpr with kind = EApp (clos, arg) }, AVPartialApplied (name, arity, overloads, ids, applied)
        | _ ->
            return { inExpr with kind = EApp (clos, arg) }, AVType inExpr.data
    | ELam (x, t) ->
        let! body, _ = gatherOverloadsExpr t
        return { inExpr with kind = ELam (x, body) }, AVType inExpr.data
    | ELet (x, v, t) ->
        let! value, valueval = gatherOverloadsExpr v
        let! body, bodyval = local (fun tenv -> evalPattern tenv x valueval) (gatherOverloadsExpr t)
        return { inExpr with kind = ELet (x, value, body) }, bodyval
    | EGroup (bs, rest) ->
        let! bss =
            mapM (fun (x, v) -> lower {
                let! value, _ = gatherOverloadsExpr v
                return x, value
            }) bs
        let! rest, restval = gatherOverloadsExpr rest
        return { inExpr with kind = EGroup (bss, rest) }, restval
    | EIf (c, tr, fl) ->
        let! cond, _ = gatherOverloadsExpr c
        let! trueb, truebval = gatherOverloadsExpr tr
        let! falseb, falsebval = gatherOverloadsExpr fl
        return { inExpr with kind = EIf (cond, trueb, falseb) }, combinePartials truebval falsebval
    | ETuple (es) ->
        let! res = mapM gatherOverloadsExpr es
        let es, esvals = List.unzip res
        return { inExpr with kind = ETuple (es) }, AVTuple esvals
    | EMatch (e, xs) ->
        let! e, _ = gatherOverloadsExpr e
        let! xss =
            mapM (fun (pat, body) -> lower {
                let! value = gatherOverloadsExpr body
                return pat, value 
            }) xs
        let pats, rest = List.unzip xss
        let rest, restvals = List.unzip rest
        let restvals =
            if List.length restvals = 0 then
                AVType inExpr.data
            else
                List.fold combinePartials (List.head restvals) restvals
        return { inExpr with kind = EMatch (e, List.zip pats rest) }, restvals 
    | ERaw (_, _) ->
        return inExpr, AVType inExpr.data
    }

let gatherOverloadsDecl (decl: TypedDecl) : LowerM<AbstractTermEnv * TypedDecl> = lower {
    let! tenv = ask
    match decl.kind with
    | DExpr expr -> 
        let! expr, _ = gatherOverloadsExpr expr
        return tenv, { decl with kind = DExpr expr }
    | DLet (pat, expr) ->
        let! e, v = gatherOverloadsExpr expr
        let! tenv = ask
        let bindings = matchPattern tenv pat v
        return extendEnv tenv bindings, { decl with kind = DLet (pat, e) }
    | DGroup (es) -> // TODO Bindings
        let! exprs =
            mapM (fun (a, b) -> lower {
                let! b, _ = gatherOverloadsExpr b 
                return a, b
            }) es
        return tenv, { decl with kind = DGroup exprs }
    | DUnion (name, tvs, cases) ->
        return tenv, { decl with kind = DUnion (name, tvs, cases) }
    | DClass (blankets, pred, impls) ->
        return tenv, { decl with kind = DClass (blankets, pred, impls) } // TODO: Checking?
    | DMember (pred, impls) ->
        let addMember (s, e) = lower {
            let! tenv = ask
            match lookup tenv s with
            | Some (AVPartialTemplate (name, arity, overloads)) ->
                return fun tenv -> extend tenv s (AVPartialTemplate (name, arity, e :: overloads))
            | _ ->
                let ty = snd (getExprType e)
                return fun tenv -> extend tenv s (AVPartialTemplate (s, calcArityType ty, [e]))
        }
        let! mappers = mapM addMember impls
        let mapper = List.fold (>>) id mappers
        return mapper tenv, { decl with kind = DMember (pred, impls) }
    }

let monomorphizePrograms (decls: TypedProgram list) : TypedProgram list =
    let res, (overloads, _) = runReaderStateM (readOverPrograms gatherOverloadsDecl decls) Map.empty (Map.empty, 0)
    match res with
    | Ok mdecls ->
        mdecls
        |> List.map (fun (name, lst) -> 
            name,
            lst |> List.map (mapTypedDecl (fun ex ->
                match ex with
                | EVar (name) when name.StartsWith(monomorphPrefix) -> // TODO: Unsafe
                    let id = int <| name.Substring(monomorphPrefix.Length)
                    match lookup overloads id with
                    | Some mangled -> EVar (mangled)
                    | _ -> ex // TODO: This is the case where a monomorphable type is ambiguous, should report it
                | _ -> ex
                ) id))
    | _ -> decls

type ShadowEnv = Map<string, int>
type ShadowM<'t> = ReaderM<ShadowEnv, 't, ErrorInfo>
let shadow = state
let getShadowEnv = ask
let setShadowEnv env = modify (fun (_, s) -> env, s)
let renameShadowed name = shadow {
    let! senv = getShadowEnv
    match lookup senv name with
    | Some v ->
        if v = 0 then return name
        else return sprintf "$%s%i" name v
    | _ -> return name
} 

let rec renameShadowedVarsInPattern (pat: Pattern) : ShadowM<Pattern> = shadow {
    match pat with
    | PName a ->
        return! fmap PName <| renameShadowed a
    | PConstant _ ->
        return pat
    | PTuple pats ->
        let! pats = mapM renameShadowedVarsInPattern pats
        return PTuple pats
    | PUnion (case, ipat) ->
        match ipat with
        | Some ipat ->
            let! rpat = renameShadowedVarsInPattern ipat
            return PUnion (case, Some rpat)
        | _ ->
            return pat
}

let shadowNewName (pat: Pattern) : ShadowM<Pattern * (ShadowEnv -> ShadowEnv)> = shadow {
    let! senv = getShadowEnv
    let rec cont names senv =
        match names with
        | [] -> senv
        | name :: rest ->
            let senv = extend senv name (1 + (lookup senv name |> Option.defaultValue (-1)))
            cont rest senv
    let senv = cont (freeInPattern pat |> Set.toList) senv
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

// TODO: Use ReprUtil for this
let rec renameShadowedVarsInExpr (inExpr: TypedExpr) : ShadowM<TypedExpr> = shadow {
    match inExpr.kind with
    | ELit (_) ->
        return inExpr
    | EOp (l, op, r) ->
        let! e1 = renameShadowedVarsInExpr l
        let! e2 = renameShadowedVarsInExpr r
        return { inExpr with kind = EOp (e1, op, e2) }
    | EVar (a) ->
        let! renamed = renameShadowed a
        return { inExpr with kind = EVar (renamed) }
    | EApp (f, x) ->
        let! clos = renameShadowedVarsInExpr f
        let! arg = renameShadowedVarsInExpr x
        return { inExpr with kind = EApp (clos, arg) }
    | ELam (x, t) ->
        let! pat, mapper = shadowNewName x
        let! body = local mapper (renameShadowedVarsInExpr t)
        return { inExpr with kind = ELam (pat, body) }
    | ELet (x, v, t) ->
        let! pat, mapper = shadowNewName x
        let! value = renameShadowedVarsInExpr v
        let! body = local mapper (renameShadowedVarsInExpr t)
        return { inExpr with kind = ELet (pat, value, body) }
    | EGroup (bs, rest) ->
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
        return { inExpr with kind = EGroup (bsss, rest) }
    | EIf (c, tr, fl) ->
        let! cond = renameShadowedVarsInExpr c
        let! trueb = renameShadowedVarsInExpr tr
        let! falseb = renameShadowedVarsInExpr fl
        return { inExpr with kind = EIf (cond, trueb, falseb) }
    | ETuple (es) ->
        let! res = mapM renameShadowedVarsInExpr es
        return { inExpr with kind = ETuple (res) }
    | EMatch (e, xs) ->
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
        return { inExpr with kind = EMatch (e, List.zip pats rest) }
    | ERaw (_, _) ->
        return inExpr
    }

let renamedShadowedVarsInDecl (decl: TypedDecl) : ShadowM<TypedDecl> = shadow {
    match decl.kind with
    | DExpr expr -> 
        let! expr = renameShadowedVarsInExpr expr
        return { decl with kind = DExpr expr }
    | DLet (pat, expr) ->
        let! e = renameShadowedVarsInExpr expr
        let! pat, mapper = shadowNewName pat
        let! senv = getShadowEnv
        do! setShadowEnv (mapper senv)
        return { decl with kind = DLet (pat, e) }
    | DGroup (es) -> // TODO Bindings
        let! exprs =
            mapM (fun (pat, e) -> lower {
                let! e = renameShadowedVarsInExpr e
                let! pat, mapper = shadowNewName (PName pat)
                let pat = match pat with PName n -> n | _ -> "$failure"
                let! senv = getShadowEnv
                do! setShadowEnv (mapper senv)
                return pat, e
            }) es
        return { decl with kind = DGroup exprs }
    | DUnion (name, tvs, cases) ->
        return { decl with kind = DUnion (name, tvs, cases) }
    | DClass (blankets, pred, impls) ->
        return { decl with kind = DClass (blankets, pred, impls) }
    | DMember (pred, impls) ->
        let! impls = 
            mapM (fun (name, expr) -> lower {
                let! expr = renameShadowedVarsInExpr expr
                return name, expr
            }) impls
        return { decl with kind = DMember (pred, impls) }
    }

let renamedShadowedVarsInPrograms (decls: TypedProgram list) : TypedProgram list =
    let names, ds = List.unzip decls
    let res = runReaderM (mapM (mapM renamedShadowedVarsInDecl) ds) Map.empty
    match res with
    | Ok mdecls -> List.zip names mdecls
    | _ -> decls

let lowerPrograms = monomorphizePrograms >> renamedShadowedVarsInPrograms