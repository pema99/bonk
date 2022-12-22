// Utilities for working with various program representations

module ReprUtil

open Repr
open Monad

// Env helpers
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env
let extendEnv env up = List.fold (fun env (name, v) -> extend env name v) env up

// Like Haskell traverse
let rec traverseTypedExpr (mapper: TypedExpr -> ReaderStateM<'a,'b,TypedExpr>) (ex: TypedExpr) : ReaderStateM<'a,'b,TypedExpr> = state {
    let! mapped = mapper ex
    match mapped with
    | TELit (pt, v) ->
        return TELit (pt, v)
    | TEVar (pt, a) ->
        return TEVar (pt, a)
    | TEApp (pt, f, x) ->
        let! f = traverseTypedExpr mapper f
        let! x = traverseTypedExpr mapper x
        return TEApp (pt, f, x) 
    | TELam (pt, x, e) ->
        let! e = traverseTypedExpr mapper e
        return TELam (pt, x, e)
    | TELet (pt, x, e1, e2) ->
        let! e1 = traverseTypedExpr mapper e1
        let! e2 = traverseTypedExpr mapper e2
        return TELet (pt, x, e1, e2)
    | TEIf (pt, cond, tr, fl) ->
        let! cond = traverseTypedExpr mapper cond
        let! tr = traverseTypedExpr mapper tr
        let! fl = traverseTypedExpr mapper fl
        return TEIf (pt, cond, tr, fl)
    | TEOp (pt, l, op, r) ->
        let! l = traverseTypedExpr mapper l
        let! r = traverseTypedExpr mapper r
        return TEOp (pt, l, op, r)
    | TETuple (pt, es) ->
        let! es = mapM (traverseTypedExpr mapper) es
        return TETuple (pt, es)
    | TEMatch (pt, e, bs) ->
        let! e = traverseTypedExpr mapper e
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr mapper) bs
        return TEMatch (pt, e, List.zip bs1 bs2)
    | TEGroup (pt, bs, rest) ->
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr mapper) bs
        let! rest = traverseTypedExpr mapper rest
        return TEGroup (pt, List.zip bs1 bs2, rest)
    | TERaw (pt, body) ->
        return TERaw (pt, body)
    }

// Replace a type in a typed expression
let replaceType (ex: TypedExpr) (ty: QualType) : TypedExpr =
    match ex with
    | TELit (pt, v)           -> TELit (ty, v)
    | TEVar (pt, a)           -> TEVar (ty, a)
    | TEApp (pt, f, x)        -> TEApp (ty, f, x) 
    | TELam (pt, x, e)        -> TELam (ty, x, e)
    | TELet (pt, x, e1, e2)   -> TELet (ty, x, e1, e2)
    | TEIf (pt, cond, tr, fl) -> TEIf (ty, cond, tr, fl)
    | TEOp (pt, l, op, r)     -> TEOp (ty, l, op, r)
    | TETuple (pt, es)        -> TETuple (ty, es)
    | TEMatch (pt, e, bs)     -> TEMatch (ty, e, bs)
    | TEGroup (pt, a, b)      -> TEGroup (ty, a, b)
    | TERaw (pt, body)        -> TERaw (ty, body)

// Get type out of a typed expression
let getExprType ex = 
    match ex with
    | TELit (pt, v)           -> pt
    | TEVar (pt, a)           -> pt
    | TEApp (pt, f, x)        -> pt
    | TELam (pt, x, e)        -> pt
    | TELet (pt, x, e1, e2)   -> pt
    | TEIf (pt, cond, tr, fl) -> pt
    | TEOp (pt, l, op, r)     -> pt
    | TETuple (pt, es)        -> pt
    | TEMatch (pt, e, bs)     -> pt
    | TEGroup (pt, a, b)      -> pt
    | TERaw (pt, body)        -> pt

// Monadic map over a typed expression
let rec mapTypeInTypedExpr (s: QualType -> ReaderStateM<'a,'b,QualType>) (ex: TypedExpr) : ReaderStateM<'a,'b,TypedExpr> =
    traverseTypedExpr (fun ex -> state {
        let pt = getExprType ex
        let! npt = s pt
        return replaceType ex npt
    }) ex

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

// Haskell traverse again, but for decls
let traverseTypedDecl (exMapper: TypedExpr -> ReaderStateM<'a,'b,TypedExpr>) (declMapper: TypedDecl -> ReaderStateM<'a,'b,TypedDecl>) (decl: TypedDecl) : ReaderStateM<'a,'b,TypedDecl> = state {
    let! decl = declMapper decl
    match decl with
    | TDExpr expr -> 
        let! expr = exMapper expr
        return TDExpr expr
    | TDLet (pat, expr) -> 
        let! expr = exMapper expr
        return TDLet (pat, expr)
    | TDGroup (es) -> 
        let exprs = List.map snd es
        let! exprs = mapM (traverseTypedExpr exMapper) exprs
        return TDGroup (List.zip (List.map fst es) exprs)
    | TDUnion (name, tvs, cases) -> 
        return TDUnion (name, tvs, cases)
    | TDClass (blankets, pred, impls) -> 
        return TDClass (blankets, pred, impls)
    | TDMember (blankets, pred, impls) -> 
        return TDMember (blankets, pred, impls)
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