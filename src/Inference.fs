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

// Environment helpers
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env
let getSubstitution = fun (r, (c, d)) -> Ok c, (r, (c, d))
let setSubstitution x = fun (r, (c, d)) -> Ok (), (r, (x, d)) 
let getTypeEnv = fun ((a, b, c), s) -> Ok a, ((a, b, c), s)
let getUserEnv = fun ((a, b, c), s) -> Ok b, ((a, b, c), s)
let getClassEnv = fun ((a, b, c), s) -> Ok c, ((a, b, c), s)
let inTypeEnv x m = local (fun (te, ue, ce) -> x, ue, ce) m
let inUserEnv x m = local (fun (te, ue, ce) -> te, x, ce) m
let inClassEnv x m = local (fun (te, ue, ce) -> te, ue, x) m
let withTypeEnv x sc m = local (fun (te, ue, ce) -> extend te x sc, ue, ce) m
let withUserEnv x sc m = local (fun (te, ue, ce) -> te, extend ue x sc, ce) m
let withClassEnv x sc m = local (fun (te, ue, ce) -> te, ue, extend ce x sc) m

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

// Instantiate a monotype from a polytype
let instantiate (sc: Scheme) : InferM<QualType> = infer {
    let (s, t) = sc
    let! ss = mapM (fun _ -> fresh) s
    let v = List.zip s ss |> Map.ofList
    return applyQualType v t // TODO: Is this right
}

// Generalize a monotype to a polytype
let generalize (t: Type) : InferM<Scheme> = infer {
    let! env = getTypeEnv
    return (Set.toList <| Set.difference (ftvType t) (ftvEnv env), ([], t)) // TODO: Sus
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
    return! simplify qs
    }

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

// Given a pattern and a type to match, recursively walk the pattern and type, gathering information along the way.
// Information gathered is in form of substitutions and changes to the typing environment (bindings). If the 'poly'
// flag is set false, bindings will not be polymorphized.
let rec gatherPatternConstraints (env: TypeEnv) (pat: Pat) (ty: Type) (poly: bool) : InferM<TypeEnv> = infer {
    match pat, ty with
    // Name patterns match with anything
    | PName a, ty ->
        let! nt = inTypeEnv env (if poly then generalize ty else just (toScheme ty)) // TODO: Check
        return extend env a nt
    // Constants match with anything that matches the type
    | PConstant v, ty ->
        let! _, t1 = inTypeEnv env (inferType (ELit v)) // TODO: Sus
        do! unify ty t1
        return env
    // Tuple patterns match with same-sized tuples
    | PTuple pats, TCtor (KProduct, typs) when List.length pats = List.length typs ->
        let! env = foldM (fun env (p, ty) -> infer {
                        return! gatherPatternConstraints env p ty poly
                    }) env (List.zip pats typs)
        return env
    // Tuple patterns match with type variables if types match
    | PTuple pats, TVar b ->
        let! tvs = mapM (fun _ -> fresh) pats
        let! env = foldM (fun env (p, ty) -> infer {
                        return! gatherPatternConstraints env p ty poly
                    }) env (List.zip pats tvs)
        let surf = Map.ofList [b, (TCtor (KProduct, tvs))]
        let! subs = getSubstitution
        do! setSubstitution (compose subs surf)
        return env
    // Union patterns match with existant unions
    | PUnion (case, pat), ty ->
        // Check if the variant constructor exists
        match lookup env case with
        | Some sc ->
            // Instantiate it with new fresh variables
            match! instantiate sc with
            | _, TArrow (inp, TCtor (KSum name, oup)) -> // TODO: Sus
                // Make a fresh type variable for the pattern being bound
                let! tv = fresh
                // Gather constrains from the inner pattern matched with the fresh type variable
                let! env = gatherPatternConstraints env pat tv poly
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                do! unify (TArrow (inp, TCtor (KSum name, oup))) (TArrow (tv, ty))
                return env
            | _ -> return! failure <| sprintf "Invalid union variant used '%s'." case
        | _ -> return! failure <| sprintf "Invalid union variant used '%s'." case
    | a, b -> return! failure <| sprintf "Could not match pattern '%A' with type '%s'." a (prettyType b)
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`. Poly flag implies whether to polymorphise (only for lets).
and inferBinding (pat: Pat) (e1: Expr) (e2: Expr) (poly: bool) : InferM<QualType> = infer {
    // Infer the type of the value being bound
    let! (p1, t1) = inferType e1
    // Gather constraints (substitutions, bindings) from the pattern
    let! env = getTypeEnv
    let! env = gatherPatternConstraints env pat t1 poly
    // Infer the body/rhs of the binding under the gathered constraints
    let! (p2, t2) = inTypeEnv env (inferType e2)
    return (p1 @ p2, t2)
    }

// Main inference
and inferType (e: Expr) : InferM<QualType> = infer {
    // Before we infer a type, apply the current substitution to the environment
    let! env = getTypeEnv
    let! subs1 = getSubstitution
    // Next, infer the type in the new environment
    let! res = inTypeEnv (applyEnv subs1 env) (inferTypeInner e)
    // After that, collect any new substitutions from the previous inference
    let! subs2 = getSubstitution
    // And apply those along with the initial ones to inferred type
    return applyQualType (compose subs1 subs2) res // TODO: Is this right?
    }

and inferTypeInner (e: Expr) : InferM<QualType> =
    match e with
    | ELit (LUnit _) -> just ([], tUnit)
    | ELit (LInt _) -> just ([], tInt)
    | ELit (LBool _) -> just ([], tBool)
    | ELit (LFloat _) -> just ([], tFloat)
    | ELit (LString _) -> just ([], tString)
    | ELit (LChar _) -> just ([], tChar)
    | EVar a -> infer {
        let! env = getTypeEnv
        match lookup env a with
        | Some s -> return! instantiate s
        | None -> return! failure <| sprintf "Use of unbound variable '%s'." a
        }
    | EApp (f, x) -> infer {
        let! tv = fresh
        let! (p1, t1) = inferType f
        let! (p2, t2) = inferType x
        do! unify t1 (TArrow (t2, tv))
        return (p1 @ p2, tv) 
        }
    | ELam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh
            let! env = getTypeEnv
            let! (p1, t1) = withTypeEnv x (toScheme tv) (inferType e)
            return (p1, TArrow (tv, t1))
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            let! env = getTypeEnv
            let! env = gatherPatternConstraints env (PTuple x) (TCtor (KProduct, tvs)) false
            let! (p1, t1) = inTypeEnv env (inferType e)
            return (p1, TArrow (TCtor (KProduct, tvs), t1))
        | _->
            return! failure <| sprintf "Unimplemented match in lambda. Couldn't match '%A' with '%A'." e x
        }
    | ELet (x, e1, e2) ->
        inferBinding x e1 e2 true
    | EIf (cond, tr, fl) -> infer {
        let! (p1, t1) = inferType cond
        let! (p2, t2) = inferType tr
        let! (p3, t3) = inferType fl
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        return (p1 @ p2 @ p3, t2)
        }
    | EOp (l, op, r) -> infer {
        let! (p1, t1) = inferType l
        let! (p2, t2) = inferType r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! (p3, inst) = instantiate scheme
        let! s3 = unify (TArrow (t1, TArrow (t2, tv))) inst
        return (p1 @ p2 @ p3, tv)
        }
    | ETuple es -> infer {
        let! scs = mapM inferType es
        let ps, typs = List.unzip scs
        return (List.concat ps, TCtor (KProduct, typs))
        }
    | EUnion (name, typs, cases, body) -> infer {
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
        let! nenv = foldM (fun acc (case, typ) -> infer {
                            let! sc = generalize (TArrow (typ, ret))
                            return extend acc case sc
                            }) env cases 
        // Finally, infer the resulting type in the new environment
        return! inTypeEnv nenv (inUserEnv nusr (inferType body))
        }
    | EMatch (e, bs) -> infer {
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! scs = mapM (fun (pat, expr) -> infer {
            return! inferBinding pat e expr false }) bs
        let ps, typs = List.unzip scs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify l r) uni
        // Compose all intermediate substitutions
        return (List.concat ps, List.head typs)
        }
    | ERec e -> infer {
        let! (p1, t1) = inferType e
        let! tv = fresh
        do! unify (TArrow (tv, tv)) t1
        return (p1, tv)
        }

// Helpers to run
let inferProgramRepl typeEnv count e =
    let cont = 
        infer {
            let! (ps, res) = inferType e
            let! ps = reduce ps
            let! subs = getSubstitution
            return applyQualType subs (ps, res)
        }
    cont ((typeEnv, Map.empty, classes), (Map.empty, count))
    |> fun (ty, ((a,b,c),(d,i))) ->
        match ty with
        | Ok (ty) -> Ok ty, i
        | Error a -> Error (sprintf "%s" a), i

let inferProgram =
    inferProgramRepl (funSchemes) 0 >> fst