// Hindley-Milner type inference
// Resources:
// - https://course.ccs.neu.edu/cs4410sp19/lec_type-inference_notes.html
// - http://dev.stephendiehl.com/fun/006_hindley_milner.html#inference-monad
// - https://jgbm.github.io/eecs662f17/Notes-on-HM.html
// - https://gist.github.com/chrisdone/0075a16b32bfd4f62b7b
// - Types and Programming Languages by Benjamin C. Pierce

module Inference

open Repr
open ReprUtil
open Monad
open Pretty
open Prelude
open Semantics

// Substitutions
type Substitution = Map<string, Type>
let compose s1 s2 = Map.fold (fun acc k v -> Map.add k v acc) s1 s2
let composeAll lst = List.fold compose Map.empty lst

// Inference monad is a reader and state monad transformed with a result monad
// The reader environment contains the known typed variables. 
// The state is the current set of substitutions as well as an integer for generatin fresh names.
// The span is the last known good position.
type InferM<'t> = ReaderStateM<TypeEnv * UserEnv * ClassEnv * Span, Substitution * int, 't, ErrorInfo>
let infer = state
let fresh : InferM<Type> = fun ((te, ue, ce, err), (s, c)) -> Ok (TVar (sprintf "_t%A" c)), ((te, ue, ce, err), (s, c + 1))

// Substitution application up to fixed point
let rec fixedPoint f s t =
    let subst = f s t
    if subst = t then subst
    else fixedPoint f s subst

let rec ftvType (t: Type) : string Set =
    match t with
    | TConst _ -> Set.empty
    | TVar a -> Set.singleton a
    | TCtor (_, args) -> args |> List.map ftvType |> List.fold Set.union Set.empty

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TConst _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TCtor (KVar name, args) ->
            match Map.tryFind name s with
            | Some (TCtor (kind, _)) -> TCtor (kind, List.map (applyTypeFP s) args)
            | Some (TVar n) -> TCtor (KVar n, List.map (applyTypeFP s) args)
            | _ -> t
        | TCtor (kind, args) -> TCtor (kind, List.map (applyTypeFP s) args)
    fixedPoint applyTypeFP

let ftvQualType (t: QualType) : Set<string> =
    let wide = Set.map (snd >> ftvType) (fst t)
    Set.union (wide |> Set.fold Set.union Set.empty) (ftvType (snd t))

let applyQualType =
    let applyQualTypeFP (s: Substitution) (t: QualType) : QualType =
        let p, ty = t
        Set.map (fun (a, b) -> a, applyType s b) p, applyType s ty
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
let getSubstitution = fun (r, (c, d)) -> Ok c, (r, (c, d))
let setSubstitution x = fun (r, (_, d)) -> Ok (), (r, (x, d))
let getCurrSpan = fun ((a, b, c, d), s) -> Ok d, ((a, b, c, d), s)
let withSpan x m = local (fun (te, ue, ce, _) -> te, ue, ce, x) m
let withSpanOf (x: UntypedExpr) m = local (fun (te, ue, ce, _) -> te, ue, ce, x.span) m
let getTypeEnvRaw = fun ((a, b, c, d), s) -> Ok a, ((a, b, c, d), s)
let getUserEnv = fun ((a, b, c, d), s) -> Ok b, ((a, b, c, d), s)
let getClassEnv = fun ((a, b, c, d), s) -> Ok c, ((a, b, c, d), s)
let inTypeEnv x m = local (fun (_, ue, ce, sp) -> x, ue, ce, sp) m
let inUserEnv x m = local (fun (te, _, ce, sp) -> te, x, ce, sp) m
let inClassEnv x m = local (fun (te, ue, _, sp) -> te, ue, x, sp) m
let withTypeEnv x sc m = local (fun (te, ue, ce, sp) -> extend te x sc, ue, ce, sp) m
let withUserEnv x sc m = local (fun (te, ue, ce, sp) -> te, extend ue x sc, ce, sp) m
let withClassEnv x sc m = local (fun (te, ue, ce, sp) -> te, ue, extend ce x sc, sp) m
let getTypeEnv = infer { // This just applies the current substitution whenever we get the environment
    let! env = getTypeEnvRaw
    let! subs = getSubstitution
    return applyEnv subs env
}
let addClassInstance (cls: ClassEnv) (name: string, inst: Type) : ClassEnv =
    match lookup cls name with
    | Some (reqs, impls) -> extend cls name (reqs, inst :: impls)
    | None -> cls

// Errors
let typeError str = infer {
    let! sp = getCurrSpan
    return! failure { msg = str; span = sp }
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
    ([], (Set.empty, t))

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
        return! typeError <| sprintf "Failed to unify types [%s] and [%s]." (prettyConcat t1) (prettyConcat t2)
    }

and mgu (t1: Type) (t2: Type) : InferM<Substitution> = infer {
    match t1, t2 with
    | a, b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        return! mguList lts rts
    | TCtor (KVar name, lts), TCtor (_, rts) when List.length lts = List.length rts ->
        // TODO: Occurs check
        let! subs = mguList lts rts
        return extend subs name t2 
    | TCtor (_, rts), TCtor (KVar name, lts) when List.length lts = List.length rts ->
        // TODO: Occurs check
        let! subs = mguList lts rts
        return extend subs name t1
    | _ ->
        return! typeError <| sprintf "Failed to unify types '%s' and '%s'." (prettyType t1) (prettyType t2)
    }

// Unify two types and store the resulting substitution
let unify (t1: Type) (t2: Type) : InferM<unit> = infer {
    let! subs = getSubstitution
    let! u = mgu (applyType subs t1) (applyType subs t2)
    do! setSubstitution (compose subs u)
}

// Get the superclasses of a typeclass
let supers (i: string) : InferM<string list> = infer {
    let! cls = getClassEnv
    match lookup cls i with
    | Some (is, _) -> return is
    | None -> return []
    }

// Given a predicate, which predicates must also hold by superclass relations?
let rec bySuper (p: Pred) : InferM<Pred Set> = infer {
    let i, t = p
    let! res = (supers i) >>= mapM (fun j -> bySuper (j, t))
    return List.fold Set.union Set.empty res
    }

// Is predicate in head normal form?
let isHNF (p: Pred) : bool =
    let rec cont p = 
        match p with
        | TVar _ -> true
        | TConst _ -> false
        | TCtor (_, _) -> false
    cont (snd p) // TODO: Is this fine?

// Convert a list of predicate to head normal form.
let rec toHNFs (ps: Pred Set) : InferM<Pred Set> = infer {
    let! res = mapM toHNF (Set.toList ps)
    return List.fold Set.union Set.empty res
    }

// Convert a single predicate to head normal form if possible.
and toHNF (p: Pred) : InferM<Pred Set> = infer {
    if isHNF p then return Set.singleton p
    else return! bySuper p >>= toHNFs
    }

// Check if a predicate tells us anything about a type
let isRelevant (ty: Type) (p: Pred) : bool =
    let tvs = ftvType ty
    match p with
    | (_, TVar a) -> Set.contains a tvs
    | _ -> true

// Is a given type an instance of a given typeclass?
// TODO: This is very basic constraint solving. Need something more sophisticated.
let instanceOf ((_, instances): Class) (ty: Type) : InferM<bool> = infer {
    match ty with
    | TConst tc ->
        return List.contains (TConst tc) instances
    | TCtor _ ->
        // Technically this should apply to type vars as well, but my logic is too brittle for that.
        let! state = get
        let overloads = List.map (fun impl -> fst <| mgu ty impl state) instances
        let anyValid = List.exists (function Ok _ -> true | _ -> false) overloads
        return anyValid
    | _ ->
        return true
    }

// Check if a predicate is is stating an illegal fact.
let checkPredicate (p: Pred) : InferM<unit> = infer {
    let (name, ty) = p
    let! cls = getClassEnv
    let klass = lookup cls name
    if not <| Option.isSome klass then
        return! typeError <| sprintf "Typeclass '%s' does not exist." name
    let! valid = instanceOf (Option.get klass) ty
    if not valid then
        return! typeError <| sprintf "Typeclass '%s' does not have an instance for '%s'." name (prettyType ty)
    }

// Reduce a list of predicates via reduction and check constraints.
let reduce (ps: Pred Set) : InferM<Pred Set> = infer {
    do! mapM_ checkPredicate (Set.toList ps)
    return! toHNFs ps
    }

// Gather all usages of user types in a type
let rec gatherUserTypesUsages (t: Type) : Set<string * int> =
    match t with
    | TVar _ | TConst _ -> Set.empty
    | TCtor (kind, lts) ->
        let inner = List.map gatherUserTypesUsages lts
        let inner = List.fold Set.union Set.empty inner
        match kind with
        | KSum name -> Set.add (name, List.length lts) inner
        | _ -> inner

// Check if a usage of a user type is valid (correct arity)
let rec checkUserTypeUsage (usr: UserEnv) (name: string, arity: int) : bool =
    match lookup usr name with
    | Some (v, _) when List.length v = arity -> true
    | _ -> false

let rec applyTypedExpr (s: Substitution) (ex: TypedExpr) : InferM<TypedExpr> =
    mapTypeInTypedExpr (applyQualType s >> just) ex

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
        let! (_, t1), _ = inTypeEnv env (inferExpr (mkExpr (ELit v) dummySpan))
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
            let! ps, ctor = instantiate sc
            // Make a fresh type variable for the pattern being bound
            let! tv = fresh
            // Gather constrains from the inner pattern matched with the fresh type variable
            let! env =
                match pat with
                | Some pat -> gatherPatternConstraints env pat (Set.union pd ps, tv) poly
                | None -> just env
            match ctor with
            | TCtor (KArrow, [inp; TCtor (KSum name, oup)]) -> 
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                do! unify (TCtor (KArrow, [inp; TCtor (KSum name, oup)])) (TCtor (KArrow, [tv; ty]))
                return env
            | TCtor (KSum name, oup) ->
                // Nullary variants
                do! unify (TCtor (KSum name, oup)) ty
                return env
            | _ -> return! typeError <| sprintf "Invalid union variant used '%s'." case
        | _ -> return! typeError <| sprintf "Invalid union variant used '%s'." case
    | a, b -> return! typeError <| sprintf "Could not match pattern '%A' with type '%s'." a (prettyQualType b)
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`. Poly flag implies whether to polymorphise (only for lets).
and inferBinding (pat: Pattern) (e1: UntypedExpr) (e2: UntypedExpr) (poly: bool) : InferM<QualType * TypedExpr * TypedExpr> = infer {
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
and inferExpr (e: UntypedExpr) : InferM<QualType * TypedExpr> = infer {
    // Infer the type in the new environment
    let! (res, ex) = inferExprInner e
    // After that, collect any new substitutions from the previous inference
    let! subs2 = getSubstitution
    // And apply those along with the initial ones to inferred type
    let ty = applyQualType subs2 res
    return ty, (replaceType ex ty)
    }

and inferExprInner (inExp: UntypedExpr) : InferM<QualType * TypedExpr> =
    withSpanOf inExp <| infer {
    match inExp.kind with
    | ELit (LUnit)     -> return let ty = (Set.empty, tUnit)   in ty, mkTypedExpr (ELit (LUnit)) ty inExp.span
    | ELit (LInt v)    -> return let ty = (Set.empty, tInt)    in ty, mkTypedExpr (ELit (LInt v)) ty inExp.span
    | ELit (LBool v)   -> return let ty = (Set.empty, tBool)   in ty, mkTypedExpr (ELit (LBool v)) ty inExp.span
    | ELit (LFloat v)  -> return let ty = (Set.empty, tFloat)  in ty, mkTypedExpr (ELit (LFloat v)) ty inExp.span
    | ELit (LString v) -> return let ty = (Set.empty, tString) in ty, mkTypedExpr (ELit (LString v)) ty inExp.span
    | ELit (LChar v)   -> return let ty = (Set.empty, tChar)   in ty, mkTypedExpr (ELit (LChar v)) ty inExp.span
    | EVar a ->
        let! env = getTypeEnv
        match lookup env a with
        | Some s ->
            let! res = instantiate s
            return res, mkTypedExpr (EVar (a)) res inExp.span
        | None -> return! typeError <| sprintf "Use of unbound variable '%s'." a
    | EApp (f, x) ->
        let! tv = fresh
        let! (p1, t1), tf = inferExpr f
        let! (p2, t2), tx = inferExpr x
        do! unify t1 (TCtor (KArrow, [t2; tv]))
        let qt = (Set.union p1 p2, tv)
        return qt, mkTypedExpr (EApp (tf, tx)) qt inExp.span
    | ELam (x, e) ->
        match x with
        | PName x ->
            let! tv = fresh
            let! _ = getTypeEnv
            let! (p1, t1), te = withTypeEnv x (toScheme tv) (inferExpr e)
            let qt = (p1, TCtor (KArrow, [tv; t1]))
            return qt, mkTypedExpr (ELam (PName x, te)) qt inExp.span
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            let! env = getTypeEnv
            let! env = gatherPatternConstraints env (PTuple x) (Set.empty, (TCtor (KProduct, tvs))) false
            let! (p1, t1), te = inTypeEnv env (inferExpr e)
            let qt = (p1, TCtor (KArrow, [TCtor (KProduct, tvs); t1]))
            return qt, mkTypedExpr (ELam (PTuple x, te)) qt inExp.span
        | _->
            return! typeError <| sprintf "Unimplemented match in lambda. Couldn't match '%A' with '%A'." e x
    | ELet (x, e1, e2) ->
        let! qt, te1, te2 = inferBinding x e1 e2 true
        return qt, mkTypedExpr (ELet (x, te1, te2)) qt inExp.span
    | EIf (cond, tr, fl) ->
        let! (p1, t1), tc = inferExpr cond
        let! (p2, t2), tt = inferExpr tr
        let! (p3, t3), tf = inferExpr fl
        do! unify t1 tBool
        do! unify t2 t3
        let qt = (Set.unionMany [p1; p2; p3], t2)
        return qt, mkTypedExpr (EIf (tc, tt, tf)) qt inExp.span
    | EOp (l, op, r) ->
        let! (p1, t1), tl = inferExpr l
        let! (p2, t2), tr = inferExpr r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! (p3, inst) = instantiate scheme
        do! unify (TCtor (KArrow, [t1; TCtor (KArrow, [t2; tv])])) inst
        let qt = (Set.unionMany [p1; p2; p3], tv)
        return qt, mkTypedExpr (EOp (tl, op, tr)) qt inExp.span
    | ETuple es ->
        let! res = mapM inferExpr es
        let scs, xs = List.unzip res
        let ps, typs = List.unzip scs
        let qt = (List.fold Set.union Set.empty ps, TCtor (KProduct, typs))
        return (qt, mkTypedExpr (ETuple xs) qt inExp.span)
    | EMatch (e, bs) ->
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! res = mapM (fun (pat, expr) -> infer {
            return! inferBinding pat e expr false }) bs
        let scs, te1, te2 = List.unzip3 res
        let ps, typs = List.unzip scs
        // Unify every match branch
        let uni = List.pairwise typs
        do! mapM_ (fun (l, r) -> unify l r) uni
        // Compose all intermediate substitutions
        let qt = (List.fold Set.union Set.empty ps, List.head typs)
        return qt, mkTypedExpr (EMatch (List.head te1, List.zip (List.map fst bs) te2)) qt inExp.span
    | EGroup (bs, rest) ->
        // Generate fresh vars for each binding, and put then in the environment
        let! tvs = mapM (fun _ -> fresh) bs
        let! env = getTypeEnv
        let names, inis = List.unzip bs
        let env = List.fold (fun env (name, tv) ->
            extend env name (toScheme tv)) env (List.zip names tvs) 
        // Infer the types of the value being bound in the new environment.
        // Recursive calls will bind to the fresh vars.
        let! res = inTypeEnv env (mapM inferExpr inis)
        let qts, tes = List.unzip res
        // Unify fresh type vas with inferred types, which may generate new substitutions. 
        // At this point, we've gathered all the substitutions from each member of the group.
        // TODO: What about about predicates?
        do! mapM_ (fun (l, r) -> unify l r) (List.zip tvs (List.map snd qts))
        // Get fully up-to-date inferred types, by applying current substitions.
        // TODO: Do I need to handle the TypedExprs here, or just QualTypes?
        let! subs = getSubstitution
        let qts = List.map (applyQualType subs) qts
        // Generalize the updated inferred types. This is where let-polymorphism happens.
        // Importantly, this happens on the in the current environment. If we did it in the
        // environment with the fresh vars, we would lose the let-polymorphism.
        let! scs = mapM generalize qts
        // Put the generalized types back into environment.
        let env = List.fold (fun env (name, sc) ->
            extend env name sc) env (List.zip names scs) 
        // Infer the body/rhs of the binding under the gathered constraints
        let! (p2, t2), te2 = inTypeEnv env (inferExpr rest)
        let qt = (p2, t2)
        return qt, mkTypedExpr (EGroup (List.zip names tes, te2)) qt inExp.span
    | ERaw (typ, body) ->
        match typ with
        | Some typ ->
            // TODO: Check typeclasses when I am able to parse QualTypes for raw blocks
            let! usr = getUserEnv
            let usages = gatherUserTypesUsages (snd typ)
            if not <| Set.forall (checkUserTypeUsage usr) usages then
                let bad =
                    Set.filter (checkUserTypeUsage usr >> not) usages
                    |> Set.map fst
                    |> String.concat ", "
                return! typeError <| sprintf "Use of undeclared type constructors in raw block: %s." bad
            return typ, mkTypedExpr (ERaw (Some typ, body)) (Set.empty, tOpaque) inExp.span
        | None ->
            return (Set.empty, tOpaque), mkTypedExpr (ERaw (Some (Set.empty, tOpaque), body)) (Set.empty, tOpaque) inExp.span
    }

// Infer and expression and then solve constraints
let inferExprTop (e: UntypedExpr) : InferM<QualType * TypedExpr> =
    withSpanOf e <| infer {
    // Infer the type of the expression
    let! qt, te = inferExpr e
    // Get the final substitution and apply it to final list of predicates
    let! subs = getSubstitution
    let! ops = reduce (Set.map (fun (q, t) -> q, applyType subs t) (fst qt))
    // Use this function to get a final type
    let fixType (ps, res) = infer {
        let res = applyType subs res
        let! npsh = 
            ps
            |> Set.map (fun (a, b) -> a, applyType subs b)
            |> reduce
        let nps =
            npsh
            |> Set.union ops
            |> Set.filter (isRelevant res)
        return (nps, res)
        }
    // Traverse the AST and get the most up to date type for each node
    // I don't do this along the way since it is expensive
    let! te = mapTypeInTypedExpr fixType te
    // Do the same for the single topmost returned type
    let! qt = fixType qt
    return qt, te
    }

// Gather variable bindings from a type and pattern
let rec gatherVarBindings (pat: Pattern) (typ: QualType) (uenv: UserEnv) : VarBinding list =
    match pat, typ with
    | PName a, typ ->
        [a, (ftvQualType typ |> Set.toList, typ)]
    | PTuple pats, (ps, TCtor (KProduct, typs)) ->
        let rep = List.replicate (List.length typs) ps
        let packed = List.zip rep typs |> List.map (fun (ps, ty) -> Set.filter (isRelevant ty) ps, ty)
        List.collect (fun (pat, va) -> gatherVarBindings pat va uenv) (List.zip pats packed)
    | PUnion (variant, Some pat), (ps, TCtor (KSum klass, tys)) ->
        instantiateVariant uenv klass variant tys
        |> Option.map (fun typ -> gatherVarBindings pat (ps, typ) uenv)
        |> Option.defaultValue []
    | _ -> [] // TODO

// Infer a declaration. Returns an update to the environment.
let rec inferDeclImmediate (inDecl: UntypedDecl) : InferM<EnvUpdate * TypedDecl> = infer {
    match inDecl.kind with
    | DExpr e ->
        let! qt, te = inferExprTop e
        return (["it", (ftvQualType qt |> Set.toList, qt)], [], [], []), mkTypedDecl (DExpr (te)) inDecl.qualifiers inDecl.span
    | DLet (name, e) ->
        let! qt, te = inferExprTop e
        let! uenv = getUserEnv
        let bindings = gatherVarBindings name qt uenv
        return (bindings, [], [], []), mkTypedDecl (DLet (name, te)) inDecl.qualifiers inDecl.span
    | DGroup (ds) ->
        let names, _ = List.unzip ds
        // TODO: This is sort of a hack, should fix
        let! res = mapM (fun name -> inferExprTop (mkExpr (EGroup (ds, (mkExpr (EVar name) dummySpan))) dummySpan)) names
        let qts, tes = List.unzip res
        let tes =
            List.zip names tes
            |> List.collect (fun (name, te) ->
                match te.kind with
                | EGroup (bs, _) -> List.filter (fst >> (=) name) bs
                | _ -> [])
        let! uenv = getUserEnv
        let bindings = List.collect (fun (a, b) -> gatherVarBindings (PName a) b uenv) (List.zip names qts)
        return (bindings, [], [], []), mkTypedDecl (DGroup (tes)) inDecl.qualifiers inDecl.span
    | DUnion (name, typs, cases) ->
        // Sum types are special since they create types, first extend the user env with the new type
        let! usr = getUserEnv
        let nusr = extend usr name (typs, cases)
        // Gather all user type usages
        let usages = List.map gatherUserTypesUsages (List.choose snd cases)
        let usages = List.fold Set.union Set.empty usages
        // If any user type usages are not to types in the user environment, error
        if not <| Set.forall (checkUserTypeUsage nusr) usages then
            let bad =
                Set.filter (checkUserTypeUsage nusr >> not) usages
                |> Set.map fst
                |> String.concat ", "
            return! typeError <| sprintf "Use of undeclared type constructors in union declaration: %s." bad
        // Gather all free type vars in each union variant
        let ftvs = List.map ftvType (List.choose snd cases)
        let ftvs = List.fold Set.union Set.empty ftvs
        let udecl = Set.filter (fun s -> not <| List.contains s typs) ftvs
        // If any of them are not explicitly declared, error
        if not <| Set.isEmpty udecl then
            let fmt = udecl |> Set.map ((+) "'" ) |> String.concat ", "
            return! typeError <| sprintf "Use of undeclared type variables in union declaration: %s." fmt
        // Guess an inferred type
        let ret = TCtor (KSum name, List.map TVar typs)
        // Put placeholder constructors for each variant in the environment
        let! _ = getTypeEnv
        let! nenv = mapM (fun (case, typ) -> infer {
                            let ctor =
                                match typ with
                                | Some v -> (TCtor (KArrow, [v; ret]))
                                | _ -> ret 
                            let! sc = generalize (Set.empty, ctor)
                            return case, sc
                         }) cases
        return (nenv, [name, (typs, cases)], [], []), mkTypedDecl (DUnion (name, typs, cases)) inDecl.qualifiers inDecl.span
    | DClass (name, reqs, mems) ->
        let vars = List.map (fun (mem, typ) -> mem, (["this"], (Set.singleton (name, TVar "this"), typ))) mems
        let cls = name, (reqs, [])
        return (vars, [], [cls], []), mkTypedDecl (DClass (name, reqs, mems)) inDecl.qualifiers inDecl.span
    | DMember (pred, exprs) ->
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
            return! typeError <| sprintf "Typeclass '%s' does not exist." name
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
                | None -> return! typeError <| sprintf "Couldn't find typeclass member '%s' of '%s'." fname name
            }) exprs
        let epreds, etyps = List.unzip eqtypes
        // Infer the actual function types from their implementations
        let names, impls = List.unzip exprs
        let! actual = mapM (inferExprTop) impls
        let aqtypes, aexprs = List.unzip actual
        let apreds, atyps = List.unzip aqtypes
        // Unify 'this' with the actual type we know it should be
        do! unify typ tv
        // Unify the actual and inferred function types.
        do! mapM_ (fun (a, b) -> unify a b) (List.zip etyps atyps)
        // Apply all substitutions thus far to the inferred types
        let! subs = getSubstitution
        let! aexprs = mapM (applyTypedExpr subs) aexprs
        // TODO: Handle the collected predicates somehow here
        // let! ps = reduce (List.concat apreds @ List.concat epreds)
        // Make the implementation to extend the class environment with
        // Return the class implementation and the type-annotated expression for each function
        return ([], [], [], [pred]), mkTypedDecl (DMember (pred, List.zip names aexprs)) inDecl.qualifiers inDecl.span
    }

// TODO: Deduplicate some of the code in Repl
// Infer a decl, update the environment underways
let rec inferDecl (d: UntypedDecl) : InferM<TypedDecl> = infer {
    let applyEnvUpdate (up: EnvUpdate) : InferM<unit> = infer {
        let! (typeEnv, userEnv, classEnv, span), other = get
        let (typeUp, userUp, classUp, implUp) = up
        let typeEnv = extendEnv typeEnv typeUp
        let userEnv = extendEnv userEnv userUp
        let classEnv = extendEnv classEnv classUp
        let classEnv = List.fold addClassInstance classEnv implUp
        do! set ((typeEnv, userEnv, classEnv, span), other)
        }
    let! envUpdate, typedDecl = inferDeclImmediate d
    do! applyEnvUpdate envUpdate
    return typedDecl
    }

// Infer entire program and return the useful parts
let inferPrograms (decls: UntypedProgram list) : Result<(UserEnv * TypedProgram list), FileErrorInfo> =
    let names, ds = List.unzip decls
    let res, ((_,userEnv,_,_),_) =
        mapM (withFileErrorInfoM (mapM inferDecl)) decls ((funSchemes, Map.empty, classes, (dummySpan)), (Map.empty, 0))
    match res with
    | Ok typedDecls -> Ok (userEnv, typedDecls)
    | Error err -> Error err
