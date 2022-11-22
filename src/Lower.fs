module Lower

open Repr
open Inference
open Monad
open Pretty

type AbstractValue =
    | AVType of QualType
    | AVPartialTemplate of int // arity
    | AVPartialApplied of int * int Set * QualType list // arity, ids, already applied
    | AVTuple of AbstractValue list
    | AVUnionCase of string * AbstractValue

let combinePartials a b =
    match a, b with
    | AVPartialApplied (a1, ids1, t1), AVPartialApplied (a2, ids2, t2) ->
        if List.length t1 > List.length t2 then // TODO: Check equality
            AVPartialApplied (a1, Set.union ids1 ids2, t1)
        else
            AVPartialApplied (a2, Set.union ids1 ids2, t2)
    | _, AVPartialApplied (a, ids, t) | AVPartialApplied (a, ids, t), _ ->
        AVPartialApplied (a, ids, t)
    | a, _ ->
        a // TODO: Check equality

type AbstractTermEnv = Map<string, AbstractValue>
type ResolvedOverloads = Map<int, string>

type LowerM<'t> = ReaderStateM<AbstractTermEnv, ResolvedOverloads * int, 't>
let lower = state
let getAbtractTermEnv = fun (ate, s) -> Ok ate, (ate, s)
let setAbtractTermEnv env = fun (ate, s) -> Ok (), (env, s)
let freshId = fun (ate, (overloads, id)) -> Ok id, (ate, (overloads, id + 1))

let rec mangleType (t: QualType) : string =
    match t with
    | _, TConst v -> v
    | _, TVar v -> sprintf "_t%s" v
    | _, TArrow (l, r) -> sprintf "%s_%s" (prettyType l) (prettyType r) 
    | _, TCtor (kind, args) ->
        match kind with
        | KProduct _ ->
            args
            |> List.map prettyType
            |> List.toArray
            |> String.concat "_"
            |> sprintf "_tup%s_"
        | KSum name ->
            let fmt =
                args
                |> List.map prettyType
                |> List.toArray
                |> String.concat "_"
            if fmt = "" then name
            else sprintf "_sum%s_name%s_" name fmt
        | _ -> "_invalid"

let mangleOverload (ts: QualType list) : string =
    ts
    |> List.map mangleType
    |> String.concat "_"

let monomorphPrefix = "_monomorph"
let getMonomorphizedName id : string =
    monomorphPrefix + string id

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
        | Some (AVPartialTemplate arity) ->
            let! id = freshId
            return TEVar (qt, getMonomorphizedName id), AVPartialApplied (arity, Set.singleton id, [])
        | Some v -> return e, v
        | _ -> return e, AVType qt
    | TEApp (qt, f, x) ->
        let! clos, closval = gatherOverloadsExpr f
        let! arg, argval = gatherOverloadsExpr x
        match closval with
        | AVPartialApplied (arity, ids, args) ->
            let applied = (getExprType x) :: args
            if arity = List.length applied then
                let! (a, (overloads, b)) = get
                let mangled = mangleOverload applied
                let overloads = Set.fold (fun acc id -> extend acc id mangled) overloads ids
                do! set (a, (overloads, b))
            return TEApp (qt, clos, arg), AVPartialApplied (arity, ids, applied)
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
        return TDClass (blankets, pred, impls) // TODO: Checking
    | TDMember (blankets, pred, impls) ->
        let addMember (s, e) = lower {
            let! tenv = getAbtractTermEnv
            if lookup tenv s = None then
                let tenv = extend tenv s (AVPartialTemplate (calcArity e))
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