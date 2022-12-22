// Utilities for working with various program representations

module ReprUtil

open Repr
open Monad

// General useful repr stuff
let mkExpr (kind: ExprKind<unit>) (span: Span) : UntypedExpr =
    { kind = kind; span = span; data = () }

let mkTypedExpr (ex: ExprKind<QualType>) (ty: QualType) (sp: Span) : TypedExpr =
    { kind = ex; data = ty; span = sp }

let mkTypedDecl (ex: DeclKind<QualType>) (sp: Span) : TypedDecl =
    { kind = ex; data = (); span = sp }

// Env helpers
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env
let extendEnv env up = List.fold (fun env (name, v) -> extend env name v) env up

// Like Haskell traverse
let rec traverseTypedExpr (mapper: TypedExpr -> ReaderStateM<'a,'b,TypedExpr>) (ex: TypedExpr) : ReaderStateM<'a,'b,TypedExpr> = state {
    let! mapped = mapper ex
    match mapped.kind with
    | ELit (v) ->
        return { mapped with kind = ELit (v) }
    | EVar (a) ->
        return { mapped with kind = EVar (a) }
    | EApp (f, x) ->
        let! f = traverseTypedExpr mapper f
        let! x = traverseTypedExpr mapper x
        return { mapped with kind = EApp (f, x)  }
    | ELam (x, e) ->
        let! e = traverseTypedExpr mapper e
        return { mapped with kind = ELam (x, e) }
    | ELet (x, e1, e2) ->
        let! e1 = traverseTypedExpr mapper e1
        let! e2 = traverseTypedExpr mapper e2
        return { mapped with kind = ELet (x, e1, e2) }
    | EIf (cond, tr, fl) ->
        let! cond = traverseTypedExpr mapper cond
        let! tr = traverseTypedExpr mapper tr
        let! fl = traverseTypedExpr mapper fl
        return { mapped with kind = EIf (cond, tr, fl) }
    | EOp (l, op, r) ->
        let! l = traverseTypedExpr mapper l
        let! r = traverseTypedExpr mapper r
        return { mapped with kind = EOp (l, op, r) }
    | ETuple (es) ->
        let! es = mapM (traverseTypedExpr mapper) es
        return { mapped with kind = ETuple (es) }
    | EMatch (e, bs) ->
        let! e = traverseTypedExpr mapper e
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr mapper) bs
        return { mapped with kind = EMatch (e, List.zip bs1 bs2) }
    | EGroup (bs, rest) ->
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr mapper) bs
        let! rest = traverseTypedExpr mapper rest
        return { mapped with kind = EGroup (List.zip bs1 bs2, rest) }
    | ERaw (a, body) ->
        return { mapped with kind = ERaw (a, body) }
    }

// Replace a type in a typed expression
let replaceType (ex: TypedExpr) (ty: QualType) : TypedExpr =
    { ex with data = ty }

// Get type out of a typed expression
let getExprType (ex: TypedExpr) : QualType = 
    ex.data

// Monadic map over a typed expression
let rec mapTypeInTypedExpr (s: QualType -> ReaderStateM<'a,'b,QualType>) (ex: TypedExpr) : ReaderStateM<'a,'b,TypedExpr> =
    traverseTypedExpr (fun ex -> state {
        let pt = getExprType ex
        let! npt = s pt
        return replaceType ex npt
    }) ex

// Map over typed expr
let rec mapTypedExpr fe (ex: TypedExpr) : TypedExpr =
    match ex.kind with
    | ELit (v)           -> { ex with kind = fe <| ELit (v) }
    | EVar (a)           -> { ex with kind = fe <| EVar (a) }
    | EApp (f, x)        -> { ex with kind = fe <| EApp (mapTypedExpr fe f, mapTypedExpr fe x)  }
    | ELam (x, e)        -> { ex with kind = fe <| ELam (x, mapTypedExpr fe e) }
    | ELet (x, e1, e2)   -> { ex with kind = fe <| ELet (x, mapTypedExpr fe e1, mapTypedExpr fe e2) }
    | EIf (cond, tr, fl) -> { ex with kind = fe <| EIf (mapTypedExpr fe cond, mapTypedExpr fe tr, mapTypedExpr fe fl) }
    | EOp (l, op, r)     -> { ex with kind = fe <| EOp (mapTypedExpr fe l, op, mapTypedExpr fe r) }
    | ETuple (es)        -> { ex with kind = fe <| ETuple (List.map (mapTypedExpr fe) es) }
    | EMatch (e, bs)     -> { ex with kind = fe <| EMatch (mapTypedExpr fe e, List.map (fun (a, b) -> a, mapTypedExpr fe b) bs) }
    | EGroup (a, b)      -> { ex with kind = fe <| EGroup (List.map (fun (a, b) -> a, mapTypedExpr fe b) a, mapTypedExpr fe b) }
    | ERaw (a, body)     -> { ex with kind = fe <| ERaw (a, body) }

// Map over typed decl
let mapTypedDecl fe fd (decl: TypedDecl) : TypedDecl = 
    match decl.kind with
    | DExpr expr                      -> { decl with kind = fd <| DExpr (mapTypedExpr fe expr) }
    | DLet (pat, expr)                -> { decl with kind = fd <| DLet (pat, mapTypedExpr fe expr) }
    | DGroup (es)                     -> { decl with kind = fd <| DGroup (List.map (fun (a, b) -> a, mapTypedExpr fe b) es) }
    | DUnion (name, tvs, cases)       -> { decl with kind = fd <| DUnion (name, tvs, cases) }
    | DClass (blankets, pred, impls)  -> { decl with kind = fd <| DClass (blankets, pred, impls) }
    | DMember (blankets, pred, impls) -> { decl with kind = fd <| DMember (blankets, pred, impls) }

// Haskell traverse again, but for decls
let traverseTypedDecl (exMapper: TypedExpr -> ReaderStateM<'a,'b,TypedExpr>) (declMapper: TypedDecl -> ReaderStateM<'a,'b,TypedDecl>) (decl: TypedDecl) : ReaderStateM<'a,'b,TypedDecl> = state {
    let! decl = declMapper decl
    match decl.kind with
    | DExpr expr -> 
        let! expr = exMapper expr
        return { decl with kind = DExpr expr }
    | DLet (pat, expr) -> 
        let! expr = exMapper expr
        return { decl with kind = DLet (pat, expr) }
    | DGroup (es) -> 
        let exprs = List.map snd es
        let! exprs = mapM (traverseTypedExpr exMapper) exprs
        return { decl with kind = DGroup (List.zip (List.map fst es) exprs) }
    | DUnion (name, tvs, cases) -> 
        return { decl with kind = DUnion (name, tvs, cases) }
    | DClass (blankets, pred, impls) -> 
        return { decl with kind = DClass (blankets, pred, impls) }
    | DMember (blankets, pred, impls) -> 
        return { decl with kind = DMember (blankets, pred, impls) }
    }

// Chain them
let traverseTypedDecls exMapper declMapper decls =
    mapM (traverseTypedDecl exMapper declMapper) decls

// Replace type vars in a type using a the passed map
let rec renameInType (map: Map<string, Type>) (ty: Type) : Type =
    match ty with
    | TVar name -> Map.tryFind name map |> Option.defaultValue ty
    | TCtor (a, tys) -> TCtor (a, List.map (renameInType map) tys)
    | TArrow (a, b) -> TArrow (renameInType map a, renameInType map b)
    | _ -> ty

// Instantiate the type of a union variant, given the class name, variant name, and types
// to instantiate generic arguments with.
let instantiateVariant (env: UserEnv) (klass: string) (variant: string) (tys: Type list) : Type =
    let (tvars, cases) = Map.find klass env
    let genCaseTy = List.find (fst >> (=) variant) cases |> snd
    let map = Map.ofList (List.zip tvars tys)
    renameInType map genCaseTy