// Hindley-Milner type inference
// Resources:
// - https://course.ccs.neu.edu/cs4410sp19/lec_type-inference_notes.html
// - http://dev.stephendiehl.com/fun/006_hindley_milner.html#inference-monad
// - https://jgbm.github.io/eecs662f17/Notes-on-HM.html
// - https://gist.github.com/chrisdone/0075a16b32bfd4f62b7b
// - Types and Programming Languages by Benjamin C. Pierce

module Inference

open Repr
open Monad
open Pretty
open Prelude

// Substitutions
type Substitution = Map<string, Type>
let compose s1 s2 = Map.fold (fun acc k v -> Map.add k v acc) s1 s2
let composeAll lst = List.fold compose Map.empty lst

// Inference monad is a reader and state monad transformed with a result monad
// The reader environment contains the known typed variables. 
// The state is the current set of substitutions as well as an integer for generatin fresh names.
type InferM<'t> = ReaderStateM<TypeEnv * UserEnv * ClassEnv, Substitution * int, 't>
let infer = state
let fresh : InferM<Type> = fun ((te, ue, ce), (s, c)) -> Ok (TVar (sprintf "_t%A" c)), ((te, ue, ce), (s, c + 1))

// Substitution application up to fixed point
let rec fixedPoint f s t =
    let subst = f s t
    if subst = t then subst
    else fixedPoint f s subst

let rec ftvType (t: Type) : string Set =
    match t with
    | TConst _ -> Set.empty
    | TVar a -> Set.singleton a
    | TArrow (t1, t2) -> Set.union (ftvType t1) (ftvType t2)
    | TCtor (_, args) -> args |> List.map ftvType |> List.fold Set.union Set.empty

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TConst _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TArrow (t1, t2) -> TArrow (applyTypeFP s t1 , applyTypeFP s t2)
        | TCtor (kind, args) -> TCtor (kind, List.map (applyTypeFP s) args)
    fixedPoint applyTypeFP

let ftvQualType (t: QualType) : Set<string> =
    let wide = List.map (snd >> ftvType) (fst t)
    Set.union (wide |> List.fold Set.union Set.empty) (ftvType (snd t))

let applyQualType =
    let applyQualTypeFP (s: Substitution) (t: QualType) : QualType =
        let p, ty = t
        List.map (fun (a, b) -> a, applyType s b) p, applyType s ty
    fixedPoint applyQualTypeFP

let ftvScheme (sc: Scheme) : string Set =
    let a, t = sc
    Set.difference (ftvQualType t) (Set.ofList a) 

let applyScheme =
    let rec applySchemeFP (s: Substitution) (sc: Scheme) : Scheme =
        let a, t = sc
        let s' = List.fold (fun acc k -> Map.remove k acc) s a
        (a, applyQualType s' t)
    fixedPoint applySchemeFP

let ftvEnv (t: TypeEnv) : Set<string> =
    let elems = t |> Map.toList |> List.map snd
    let ftv = List.fold (fun acc x -> Set.union acc (ftvScheme x)) Set.empty
    ftv elems

let applyEnv =
    let applyEnvFP (s: Substitution) (t: TypeEnv) : TypeEnv =
        Map.map (fun _ v -> applyScheme s v) t
    fixedPoint applyEnvFP

// Environment helpers
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env
let getSubstitution = fun (r, (c, d)) -> Ok c, (r, (c, d))
let setSubstitution x = fun (r, (c, d)) -> Ok (), (r, (x, d)) 
let getTypeEnvRaw = fun ((a, b, c), s) -> Ok a, ((a, b, c), s)
let getUserEnv = fun ((a, b, c), s) -> Ok b, ((a, b, c), s)
let getClassEnv = fun ((a, b, c), s) -> Ok c, ((a, b, c), s)
let inTypeEnv x m = local (fun (te, ue, ce) -> x, ue, ce) m
let inUserEnv x m = local (fun (te, ue, ce) -> te, x, ce) m
let inClassEnv x m = local (fun (te, ue, ce) -> te, ue, x) m
let withTypeEnv x sc m = local (fun (te, ue, ce) -> extend te x sc, ue, ce) m
let withUserEnv x sc m = local (fun (te, ue, ce) -> te, extend ue x sc, ce) m
let withClassEnv x sc m = local (fun (te, ue, ce) -> te, ue, extend ce x sc) m
let getTypeEnv = infer { // This just applies the current substitution whenever we get the environment
    let! env = getTypeEnvRaw
    let! subs = getSubstitution
    return applyEnv subs env
}

// Instantiate a monotype from a polytype
let instantiate (sc: Scheme) : InferM<QualType> = infer {
    let (s, t) = sc
    let! ss = mapM (fun _ -> fresh) s
    let v = List.zip s ss |> Map.ofList
    return applyQualType v t
}

// Generalize a monotype to a polytype
let generalize (t: QualType) : InferM<Scheme> = infer {
    let! env = getTypeEnv
    return (Set.toList <| Set.difference (ftvQualType t) (ftvEnv env), t)
}

// Turn a type into a trivial scheme
let toScheme (t: Type) : Scheme =
    ([], ([], t))

// Type coercien is like unification but directional. Try to find a substitution that turns
// type t1 into type t2 when applied.
let rec coerce (t1: Type) (t2: Type) : Substitution option =
    match t1, t2 with
    | a, b when a = b -> Some (Map.empty)
    | TVar a, b -> Some (Map.ofList [(a, b)])
    | TArrow (l1, r1), TArrow (l2, r2) ->
        let s1 = coerce l1 l2
        let s2 = coerce r1 r2
        Option.map2 compose s1 s2
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        let z = List.zip lts rts
        let z = List.map (fun (a, b) -> coerce a b) z
        if not <| List.forall Option.isSome z then None
        else
            let z = List.choose id z
            Some (composeAll z)
    | _ ->
        None

// Get the superclasses of a typeclass
let supers (i: string) : InferM<string list> = infer {
    let! cls = getClassEnv
    match lookup cls i with
    | Some (is, its) -> return is
    | None -> return []
    }

// Get the subclasses (instances) of a typeclass
let insts (i: string) : InferM<Inst list> = infer {
    let! cls = getClassEnv
    match lookup cls i with
    | Some (is, its) -> return its
    | None -> return []
    }

// Given a predicate, which predicates must also hold by superclass relations?
let rec bySuper (p: Pred) : InferM<Pred list> = infer {
    let i, t = p
    let! res = (supers i) >>= mapM (fun j -> bySuper (j, t))
    return List.concat res
    }

// Given a predicate, which predicates must also hold by subclass relation?
let rec byInst (p: Pred) : InferM<Pred list option> = infer {
    let i, t = p
    let tryInst (ps: Pred list, h) =
        if fst h = fst p then
            coerce (snd h) (snd p)
            |> Option.map (fun u -> List.map (fun (j, k) -> j, applyType u k) ps)
        else
            None
    let! res = insts i
    return
        res
        |> List.map tryInst
        |> List.tryPick id
    }

// Do the predicates ps semantically entail p? Ie: ps_1 .. ps_n |- p
let rec entail (ps: Pred list) (p: Pred) : InferM<bool> = infer {
    let! up = mapM bySuper ps
    let byUp = List.exists (List.contains p) up
    match! byInst p with
    | Some qs ->
        let! down = mapM (entail ps) qs
        return byUp || List.forall id down
    | None ->
        return byUp
    }

// Does predicate p always hold?
let axiom (p: Pred) : InferM<bool> =
    entail [] p

// Is type 't' definitely a member of the 'klass' typeclass?
let instOf (klass: string) (t: Type) : InferM<bool> =
    axiom (klass, t)

// Is predicate in head normal form?
let isHNF (p: Pred) : bool =
    let rec cont p = 
        match p with
        | TVar _ -> true
        | TConst _ -> false
        | TArrow (l, r) -> false
        | TCtor (_, typs) -> false
    cont (snd p) // TODO: Is this fine?

// Convert a list of predicate to head normal form.
let rec toHNFs (ps: Pred list) : InferM<Pred list> = infer {
    let! res = mapM toHNF ps
    return List.concat res
    }

// Convert a single predicate to head normal form if possible.
and toHNF (p: Pred) : InferM<Pred list> = infer {
    if isHNF p then return [p]
    else
        match! byInst p with
        | None -> return! failure <| sprintf "Failed to satisfy constraint, type '%s' is not in class '%s'." (prettyType (snd p)) (fst p)
        | Some ps -> return! toHNFs ps
    }

// Simplify a list of head normal form predicates via reduction
let simplify (p: Pred list) : InferM<Pred list> = infer {
    let rec loop rs lst = infer {
        match lst with
        | [] -> return rs
        | p :: ps ->
            let! test = entail (rs @ ps) p
            if test then return! loop rs ps
            else return! loop (p :: rs) ps
        }
    return! loop [] p
    }

// Reduce a list of predicates via reduction. Solve typeclass constraints along the way.
let reduce (ps: Pred list) : InferM<Pred list> = infer {
    let! qs = toHNFs ps
    let! res = simplify qs
    return List.distinct res
    }

// Check if a predicate tells us anything about a type
let isRelevant (ty: Type) (p: Pred) : bool =
    let tvs = ftvType ty
    match p with
    | (_, TVar a) -> Set.contains a tvs
    | _ -> true

// Unification, most general unifier
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec mguList (t1 : Type list) (t2 : Type list) : InferM<Substitution> = infer {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = mgu h1 h2
        let! s2 = mguList (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ ->
        let prettyConcat = List.map (prettyType) >> String.concat ", "
        return! failure <| sprintf "Failed to unify types [%s] and [%s]." (prettyConcat t1) (prettyConcat t2)
    }

and mgu (t1: Type) (t2: Type) : InferM<Substitution> = infer {
    match t1, t2 with
    | a, b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TArrow (l1, r1), TArrow (l2, r2) -> return! mguList [l1; r1] [l2; r2]
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        return! mguList lts rts
    | _ ->
        return! failure <| sprintf "Failed to unify types '%s' and '%s'." (prettyType t1) (prettyType t2)
    }

// Unify two types and store the resulting substitution
let unify (t1: Type) (t2: Type) : InferM<unit> = infer {
    let! subs = getSubstitution
    let! u = mgu (applyType subs t1) (applyType subs t2)
    do! setSubstitution (compose subs u)
}

// Gather all usages of user types in a type
let rec gatherUserTypesUsages (t: Type) : Set<string * int> =
    match t with
    | TVar _ | TConst _ -> Set.empty
    | TArrow (l, r) -> Set.union (gatherUserTypesUsages l) (gatherUserTypesUsages r)
    | TCtor (kind, lts) ->
        let inner = List.map gatherUserTypesUsages lts
        let inner = List.fold Set.union Set.empty inner
        match kind with
        | KSum name -> Set.add (name, List.length lts) inner
        | _ -> inner

// Check if a usage of a user type is valid (correct arity)
let rec checkUserTypeUsage (usr: UserEnv) (name: string, arity: int) : bool =
    match lookup usr name with
    | Some v when v = arity -> true
    | _ -> false

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
    | TEGroup (pt, a, b)         -> TEGroup (ty, a, b)

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

// Traverse a typed AST and apply some transformation to each type
let rec traverseTypedExpr (s: QualType -> InferM<QualType>) (ex: TypedExpr) : InferM<TypedExpr> = infer {
    match ex with
    | TELit (pt, v) ->
        let! pt = s pt
        return TELit (pt, v)
    | TEVar (pt, a) ->
        let! pt = s pt
        return TEVar (pt, a)
    | TEApp (pt, f, x) ->
        let! pt = s pt
        let! f = traverseTypedExpr s f
        let! x = traverseTypedExpr s x
        return TEApp (pt, f, x) 
    | TELam (pt, x, e) ->
        let! pt = s pt
        let! e = traverseTypedExpr s e
        return TELam (pt, x, e)
    | TELet (pt, x, e1, e2) ->
        let! pt = s pt
        let! e1 = traverseTypedExpr s e1
        let! e2 = traverseTypedExpr s e2
        return TELet (pt, x, e1, e2)
    | TEIf (pt, cond, tr, fl) ->
        let! pt = s pt
        let! cond = traverseTypedExpr s cond
        let! tr = traverseTypedExpr s tr
        let! fl = traverseTypedExpr s fl
        return TEIf (pt, cond, tr, fl)
    | TEOp (pt, l, op, r) ->
        let! pt = s pt
        let! l = traverseTypedExpr s l
        let! r = traverseTypedExpr s r
        return TEOp (pt, l, op, r)
    | TETuple (pt, es) ->
        let! pt = s pt
        let! es = mapM (traverseTypedExpr s) es
        return TETuple (pt, es)
    | TEMatch (pt, e, bs) ->
        let! pt = s pt
        let! e = traverseTypedExpr s e
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr s) bs
        return TEMatch (pt, e, List.zip bs1 bs2)
    | TEGroup (pt, bs, rest) ->
        let! pt = s pt
        let bs1 = List.map fst bs
        let! bs2 = mapM (snd >> traverseTypedExpr s) bs
        let! rest = traverseTypedExpr s rest
        return TEGroup (pt, List.zip bs1 bs2, rest)
    }

let rec applyTypedExpr (s: Substitution) (ex: TypedExpr) : InferM<TypedExpr> =
    traverseTypedExpr (applyQualType s >> just) ex

// Given a pattern and a type to match, recursively walk the pattern and type, gathering information along the way.
// Information gathered is in form of substitutions and changes to the typing environment (bindings). If the 'poly'
// flag is set false, bindings will not be polymorphized.
let rec gatherPatternConstraints (env: TypeEnv) (pat: Pattern) (ty: QualType) (poly: bool) : InferM<TypeEnv> = infer {
    match pat, ty with
    // Name patterns match with anything
    | PName a, ty ->
        let! nt = inTypeEnv env (if poly then generalize ty else just ([], ty))
        return extend env a nt
    // Constants match with anything that matches the type
    | PConstant v, (_, ty) ->
        // This is fine since literals are always unambiguous. No new predicates can occur.
        let! (_, t1), _ = inTypeEnv env (inferExpr (ELit v))
        do! unify ty t1
        return env
    // Tuple patterns match with same-sized tuples
    | PTuple pats, (pd, TCtor (KProduct, typs)) when List.length pats = List.length typs ->
        let pds = List.replicate (List.length typs) pd
        let! env = foldM (fun env (p, ty) -> infer {
                        return! gatherPatternConstraints env p ty poly
                    }) env (List.zip pats (List.zip pds typs))
        return env
    // Tuple patterns match with type variables if types match
    | PTuple pats, (pd, TVar b) ->
        let! tvs = mapM (fun _ -> fresh) pats
        let pds = List.replicate (List.length tvs) pd
        let! env = foldM (fun env (p, ty) -> infer {
                        return! gatherPatternConstraints env p ty poly
                    }) env (List.zip pats (List.zip pds tvs))
        let surf = Map.ofList [b, (TCtor (KProduct, tvs))]
        let! subs = getSubstitution
        do! setSubstitution (compose subs surf)
        return env
    // Union patterns match with existant unions
    | PUnion (case, pat), (pd, ty) ->
        // Check if the variant constructor exists
        match lookup env case with
        | Some sc ->
            // Instantiate it with new fresh variables
            match! instantiate sc with
            | ps, TArrow (inp, TCtor (KSum name, oup)) -> 
                // Make a fresh type variable for the pattern being bound
                let! tv = fresh
                // Gather constrains from the inner pattern matched with the fresh type variable
                let! env = gatherPatternConstraints env pat (pd @ ps, tv) poly
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                do! unify (TArrow (inp, TCtor (KSum name, oup))) (TArrow (tv, ty))
                return env
            | _ -> return! failure <| sprintf "Invalid union variant used '%s'." case
        | _ -> return! failure <| sprintf "Invalid union variant used '%s'." case
    | a, b -> return! failure <| sprintf "Could not match pattern '%A' with type '%s'." a (prettyQualType b)
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`. Poly flag implies whether to polymorphise (only for lets).
and inferBinding (pat: Pattern) (e1: Expr) (e2: Expr) (poly: bool) : InferM<QualType * TypedExpr * TypedExpr> = infer {
    // Infer the type of the value being bound
    let! (p1, t1), te1 = inferExpr e1
    // Gather constraints (substitutions, bindings) from the pattern
    let! env = getTypeEnv
    let! env = gatherPatternConstraints env pat (p1, t1) poly
    // Infer the body/rhs of the binding under the gathered constraints
    let! (p2, t2), te2 = inTypeEnv env (inferExpr e2)
    let qt = (p2, t2) // TODO: Should this include p1?
    return qt, te1, te2
    }

// Main inference
and inferExpr (e: Expr) : InferM<QualType * TypedExpr> = infer {
    // Before we infer a type, apply the current substitution to the environment
    let! env = getTypeEnv
    let! subs1 = getSubstitution
    // Next, infer the type in the new environment
    let! (res, ex) = inTypeEnv (applyEnv subs1 env) (inferExprInner e)
    // After that, collect any new substitutions from the previous inference
    let! subs2 = getSubstitution
    // And apply those along with the initial ones to inferred type
    let ty = applyQualType (compose subs1 subs2) res
    return ty, (replaceType ex ty)
    }

and inferExprInner (e: Expr) : InferM<QualType * TypedExpr> =
    match e with
    | ELit (LUnit)     -> let ty = ([], tUnit)   in just (ty, TELit (ty, LUnit))
    | ELit (LInt v)    -> let ty = ([], tInt)    in just (ty, TELit (ty, LInt v))
    | ELit (LBool v)   -> let ty = ([], tBool)   in just (ty, TELit (ty, LBool v))
    | ELit (LFloat v)  -> let ty = ([], tFloat)  in just (ty, TELit (ty, LFloat v))
    | ELit (LString v) -> let ty = ([], tString) in just (ty, TELit (ty, LString v))
    | ELit (LChar v)   -> let ty = ([], tChar)   in just (ty, TELit (ty, LChar v))
    | EVar a -> infer {
        let! env = getTypeEnv
        match lookup env a with
        | Some s ->
            let! res = instantiate s
            return res, (TEVar (res, a))
        | None -> return! failure <| sprintf "Use of unbound variable '%s'." a
        }
    | EApp (f, x) -> infer {
        let! tv = fresh
        let! (p1, t1), tf = inferExpr f
        let! (p2, t2), tx = inferExpr x
        do! unify t1 (TArrow (t2, tv))
        let qt = (p1 @ p2, tv)
        return qt, TEApp (qt, tf, tx)
        }
    | ELam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh
            let! env = getTypeEnv
            let! (p1, t1), te = withTypeEnv x (toScheme tv) (inferExpr e)
            let qt = (p1, TArrow (tv, t1))
            return qt, TELam (qt, PName x, te)
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            let! env = getTypeEnv
            let! env = gatherPatternConstraints env (PTuple x) ([], (TCtor (KProduct, tvs))) false
            let! (p1, t1), te = inTypeEnv env (inferExpr e)
            let qt = (p1, TArrow (TCtor (KProduct, tvs), t1))
            return qt, TELam (qt, PTuple x, te)
        | _->
            return! failure <| sprintf "Unimplemented match in lambda. Couldn't match '%A' with '%A'." e x
        }
    | ELet (x, e1, e2) -> infer {
        let! qt, te1, te2 = inferBinding x e1 e2 true
        return qt, TELet (qt, x, te1, te2)
        }
    | EIf (cond, tr, fl) -> infer {
        let! (p1, t1), tc = inferExpr cond
        let! (p2, t2), tt = inferExpr tr
        let! (p3, t3), tf = inferExpr fl
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        let qt = (p1 @ p2 @ p3, t2)
        return qt, TEIf (qt, tc, tt, tf)
        }
    | EOp (l, op, r) -> infer {
        let! (p1, t1), tl = inferExpr l
        let! (p2, t2), tr = inferExpr r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! (p3, inst) = instantiate scheme
        let! s3 = unify (TArrow (t1, TArrow (t2, tv))) inst
        let qt = (p1 @ p2 @ p3, tv)
        return qt, TEOp (qt, tl, op, tr)
        }
    | ETuple es -> infer {
        let! res = mapM inferExpr es
        let scs, xs = List.unzip res
        let ps, typs = List.unzip scs
        let qt = (List.concat ps, TCtor (KProduct, typs))
        return (qt, TETuple (qt, xs))
        }
    | EMatch (e, bs) -> infer {
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! res = mapM (fun (pat, expr) -> infer {
            return! inferBinding pat e expr false }) bs
        let scs, te1, te2 = List.unzip3 res
        let ps, typs = List.unzip scs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify l r) uni
        // Compose all intermediate substitutions
        let qt = (List.concat ps, List.head typs)
        return qt, TEMatch (qt, List.head te1, List.zip (List.map fst bs) te2)
        }
    | EGroup (bs, rest) -> infer {
        // Generate fresh vars for each binding, and put then in the environment
        let! tvs = mapM (fun _ -> fresh) bs
        let! env = getTypeEnv
        let names, inis = List.unzip bs
        let env = List.fold (fun env (name, tv) ->
            extend env name (toScheme tv)) env (List.zip names tvs) 
        // Infer the types of the value being bound in the new environment and generalize them
        let! res = inTypeEnv env (mapM inferExpr inis)
        let qts, tes = List.unzip res
        let! scs = inTypeEnv env (mapM generalize qts)
        // Put them in the environment
        let env = List.fold (fun env (name, sc) ->
            extend env name sc) env (List.zip names scs) 
        // Infer the body/rhs of the binding under the gathered constraints
        let! (p2, t2), te2 = inTypeEnv env (inferExpr rest)
        // Unify fresh tvs with inferred types // TODO: What about about predicates
        do! mapM_ (fun (l, r) -> unify l r) (List.zip tvs (List.map (snd >> snd) scs))
        let qt = (p2, t2)
        return qt, TEGroup (qt, List.zip names tes, te2)
        }

// Infer and expression and then solve constraints
let inferExprTop (e: Expr) : InferM<QualType * TypedExpr> = infer {
    // Infer the type of the expression
    let! qt, te = inferExpr e
    // Get the final substitution and apply it to final list of predicates
    let! subs = getSubstitution
    let ops = List.map (fun (q, t) -> q, applyType subs t) (fst qt)
    // Use this function to get a final type
    let fixType (ps, res) = infer {
        let res = applyType subs res
        let! nps = 
            ps @ ops
            |> List.map (fun (a, b) -> a, applyType subs b)
            |> List.filter (isRelevant res)
            |> reduce
        return applyQualType subs (nps, res)
        }
    // Traverse the AST and get the most up to date type for each node
    // I don't do this along the way since it is expensive
    let! te = traverseTypedExpr fixType te
    // Do the same for the single topmost returned type
    let! qt = fixType qt
    return qt, te
    }

// Gather variable bindings from a type and pattern
let rec gatherVarBindings (pat: Pattern) (typ: QualType) : VarBinding list =
    match pat, typ with
    | PName a, typ ->
        [a, (ftvQualType typ |> Set.toList, typ)]
    | PTuple pats, (ps, TCtor (KProduct, typs)) ->
        let rep = List.replicate (List.length typs) ps
        let packed = List.zip rep typs
        List.collect (fun (pat, va) -> gatherVarBindings pat va) (List.zip pats packed)
    | _ -> [] // TODO

// Infer a declaration. Returns an update to the environment.
let rec inferDecl (d: Decl) : InferM<EnvUpdate * TypedDecl> = infer {
    match d with
    | DExpr e ->
        let! qt, te = inferExprTop e
        return (["it", (ftvQualType qt |> Set.toList, qt)], [], [], []), TDExpr (te)
    | DLet (name, e) ->
        let! qt, te = inferExprTop e
        let bindings = gatherVarBindings name qt
        return (bindings, [], [], []), TDLet (name, te)
    | DGroup (ds) ->
        let names, exs = List.unzip ds
        // TODO: This is sort of a hack, should fix
        let! res = mapM (fun name -> inferExprTop (EGroup (ds, EVar name))) names
        let qts, tes = List.unzip res
        let tes =
            List.zip names tes
            |> List.collect (fun (name, te) ->
                match te with
                | TEGroup (pt, bs, rest) -> List.filter (fst >> (=) name) bs
                | _ -> [])
        let bindings = List.collect (fun (a, b) -> gatherVarBindings (PName a) b) (List.zip names qts)
        return (bindings, [], [], []), TDGroup (tes)
    | DUnion (name, typs, cases) ->
        // Sum types are special since they create types, first extend the user env with the new type
        let! usr = getUserEnv
        let nusr = extend usr name (List.length typs)
        // Gather all user type usages
        let usages = List.map gatherUserTypesUsages (List.map snd cases)
        let usages = List.fold Set.union Set.empty usages
        // If any user type usages are not to types in the user environment, error
        if not <| Set.forall (checkUserTypeUsage nusr) usages then
            let bad =
                Set.filter (checkUserTypeUsage nusr >> not) usages
                |> Set.map fst
                |> String.concat ", "
            return! failure <| sprintf "Use of undeclared type constructors in union declaration: %s." bad
        // Gather all free type vars in each union variant
        let ftvs = List.map (snd >> ftvType) cases
        let ftvs = List.fold Set.union Set.empty ftvs
        let udecl = Set.filter (fun s -> not <| List.contains s typs) ftvs
        // If any of them are not explicitly declared, error
        if not <| Set.isEmpty udecl then
            let fmt = udecl |> Set.map ((+) "'" ) |> String.concat ", "
            return! failure <| sprintf "Use of undeclared type variables in union declaration: %s." fmt
        // Guess an inferred type
        let ret = TCtor (KSum name, List.map TVar typs)
        // Put placeholder constructors for each variant in the environment
        let! env = getTypeEnv
        let! nenv = mapM (fun (case, typ) -> infer {
                            let! sc = generalize ([], (TArrow (typ, ret)))
                            return case, sc
                         }) cases
        return (nenv, [name, (List.length typs)], [], []), TDUnion (name, typs, cases)
    | DClass (name, reqs, mems) ->
        let vars = List.map (fun (mem, typ) -> mem, (["this"], ([name, TVar "this"], typ))) mems
        let cls = name, (reqs, [])
        return (vars, [], [cls], []), TDClass (name, reqs, mems)
    | DMember (blankets, pred, exprs) ->
        // TODO: Semantic checking
        // o Check that the typeclass exists
        // - Check that the names of the member match exactly
        // - Check that the requirements are satisfied
        // o Replace occurences of 'this' with the more specific type
        // o Check that the type of each implemented function/member matches the known type (unify)
        // o Check that we don't infer 'this' to be be something else than the known type (unify)
        // - Check overlapping implementations
        // First, check if the typeclass even exists
        let! cls = getClassEnv
        let name, typ = pred
        let klass = lookup cls name
        if not <| Option.isSome klass then
            return! failure <| sprintf "Typeclass '%s' does not exist." name
        let (reqs, instances) = Option.get klass
        // TODO: Next, check that the names of the member match exactly
        // TODO: Then, check that the requirements are satisfied
        // Gather the expected function types from the environment, with 'this' renamed to a fresh tv
        let! env = getTypeEnv
        let! tv = fresh
        let! eqtypes = 
            mapM (fun (fname, impl) -> infer {
                match lookup env fname with
                | Some (_, qt) -> return applyQualType (Map.ofList ["this", tv]) qt
                | None -> return! failure <| sprintf "Couldn't find typeclass member '%s'." name
            }) exprs
        let epreds, etyps = List.unzip eqtypes
        // Infer the actual function types from their implementations
        let names, impls = List.unzip exprs
        let! actual = mapM (inferExprTop) impls
        let aqtypes, aexprs = List.unzip actual
        let apreds, atyps = List.unzip aqtypes
        // Unify 'this' with the actual type we know it should be
        do! unify typ tv
        // Unify the actual and inferred function types. TODO: Should this be coerce?
        do! mapM_ (fun (a, b) -> unify a b) (List.zip etyps atyps)
        // Apply all substitutions thus far to the inferred types
        let! subs = getSubstitution
        let! aexprs = mapM (applyTypedExpr subs) aexprs
        // TODO: Handle the collected predicates somehow here
        // let! ps = reduce (List.concat apreds @ List.concat epreds)
        // Make the implementation to extend the class environment with
        let imp = name, (blankets, pred)
        // Return the class implementation and the type-annotated expression for each function
        return ([], [], [], [imp]), TDMember (blankets, pred, List.zip names aexprs)
    }