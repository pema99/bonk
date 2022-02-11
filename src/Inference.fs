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

// Schemes and environments
type Scheme = string list * Type
type TypeEnv = Map<string, Scheme>

// Handling for user types. Map of string to type-arity of union
type UserEnv = Map<string, int>

// Substitutions
type Substitution = Map<string, Type>
let compose s1 s2 = Map.fold (fun acc k v -> Map.add k v acc) s1 s2
let composeAll lst = List.fold compose Map.empty lst

// Inference monad is a state monad mixed with result monad
type InferM<'t> = StateM<(TypeEnv * UserEnv * Substitution * int), 't>
let infer = state
let fresh : InferM<Type> = fun (te, ue, s, c) -> Ok (TVar (sprintf "_t%A" c)), (te, ue, s, c + 1)

// Environment helpers
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env
let getTypeEnv = fun (a, b, c, d) -> Ok a, (a, b, c, d)
let getUserEnv = fun (a, b, c, d) -> Ok b, (a, b, c, d)
let getSubstitution = fun (a, b, c, d) -> Ok c, (a, b, c, d)
let setTypeEnv x = fun (a, b, c, d) -> Ok (), (x, b, c, d) 
let setUserEnv x = fun (a, b, c, d) -> Ok (), (a, x, c, d) 
let setSubstitution x = fun (a, b, c, d) -> Ok (), (a, b, x, d) 

// Substitution application
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

let ftvScheme (sc: Scheme) : string Set =
    let a, t = sc
    Set.difference (ftvType t) (Set.ofList a) 

let applyScheme =
    let rec applySchemeFP (s: Substitution) (sc: Scheme) : Scheme =
        let a, t = sc
        let s' = List.fold (fun acc k -> Map.remove k acc) s a
        (a, applyType s' t)
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
let instantiate (sc: Scheme) : InferM<Type> = infer {
    let (s, t) = sc
    let! ss = mapM (fun _ -> fresh) s
    let v = List.zip s ss |> Map.ofList
    return applyType v t
}

// Generalize a monotype to a polytype
let generalize (env: TypeEnv) (t: Type) : Scheme =
    (Set.toList <| Set.difference (ftvType t) (ftvEnv env), t)

// Unification
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec mguList (t1 : Type list) (t2 : Type list) : InferM<Substitution> = infer {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = mgu h1 h2
        let! s2 = mguList (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ -> return! failure "Unification failure"
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
        return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
    }

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
let rec gatherPatternConstraints (pat: Pat) (ty: Type) (poly: bool) : InferM<unit> = infer {
    match pat, ty with
    // Name patterns match with anything
    | PName a, ty ->
        let! env = getTypeEnv
        let nt = if poly then generalize env ty else ([], ty)
        let env = extend env a nt
        do! setTypeEnv env
    // Constants match with anything that matches the type
    | PConstant v, ty ->
        let! t1 = inferType (ELit v)
        do! unify ty t1
    // Tuple patterns match with same-sized tuples
    | PTuple pats, TCtor (KProduct, typs) when List.length pats = List.length typs ->
        do! mapM_ (fun (p, ty) -> infer {
                do! gatherPatternConstraints p ty poly
            }) (List.zip pats typs)
    // Tuple patterns match with type variables if types match
    | PTuple pats, TVar b ->
        let! tvs = mapM (fun _ -> fresh) pats
        do! mapM_ (fun (p, ty) -> infer {
                do! gatherPatternConstraints p ty poly
            }) (List.zip pats tvs)
        let surf = Map.ofList [b, (TCtor (KProduct, tvs))]
        let! subs = getSubstitution
        do! setSubstitution (compose subs surf)
    // Union patterns match with existant unions
    | PUnion (case, pat), ty ->
        // Check if the variant constructor exists
        let! env = getTypeEnv
        match lookup env case with
        | Some sc ->
            // Instantiate it with new fresh variables
            match! instantiate sc with
            | TArrow (inp, TCtor (KSum name, oup)) ->
                // Make a fresh type variable for the pattern being bound
                let! tv = fresh
                // Gather constrains from the inner pattern matched with the fresh type variable
                do! gatherPatternConstraints pat tv poly
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                do! unify (TArrow (inp, TCtor (KSum name, oup))) (TArrow (tv, ty))
            | _ -> return! failure <| sprintf "Invalid union variant %s." case
        | _ -> return! failure <| sprintf "Invalid union variant %s." case
    | a, b -> return! failure <| sprintf "Could not match pattern %A with type %A" a b
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`.
and patternMatch (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Type> = infer {
    // Infer the type of the value being bound
    let! t1 = inferType e1
    // Generalize it, if it is a polytype, we don't generalize the binding
    let! env = getTypeEnv
    let q, t1 = generalize env t1
    let poly = not <| List.isEmpty q
    // Gather constraints (substitutions, bindings) from the pattern
    do! gatherPatternConstraints pat t1 poly
    // Infer the body/rhs of the binding under the gathered constraints
    let! t3 = inferType e2
    // Apply all constraints and propagate up
    return t3
    }

// Constraint gathering
and inferType (e: Expr) : InferM<Type> =
    match e with
    | ELit (LUnit _) -> just tUnit
    | ELit (LInt _) -> just tInt
    | ELit (LBool _) -> just tBool
    | ELit (LFloat _) -> just tFloat
    | ELit (LString _) -> just tString
    | ELit (LChar _) -> just tChar
    | EVar a -> infer {
        let! env = getTypeEnv
        match lookup env a with
        | Some s -> return! instantiate s
        | None -> return! failure <| sprintf "Use of unbound variable %A." a
        }
    | EApp (f, x) -> infer {
        let! tv = fresh
        let! t1 = inferType f
        let! t2 = inferType x
        do! unify t1 (TArrow (t2, tv))
        return tv 
        }
    | ELam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh
            let! env = getTypeEnv
            do! setTypeEnv (extend env x ([], tv))
            let! t1 = inferType e
            return TArrow (tv, t1)
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            do! gatherPatternConstraints (PTuple x) (TCtor (KProduct, tvs)) false
            let! t1 = inferType e
            return TArrow (TCtor (KProduct, tvs), t1)
        | _->
            return! failure "Unimplemented match"
        }
    | ELet (x, e1, e2) ->
        patternMatch x e1 e2
    | EIf (cond, tr, fl) -> infer {
        let! t1 = inferType cond
        let! t2 = inferType tr
        let! t3 = inferType fl
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        return t2
        }
    | EOp (l, op, r) -> infer {
        let! t1 = inferType l
        let! t2 = inferType r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! inst = instantiate scheme
        let! s3 = unify (TArrow (t1, TArrow (t2, tv))) inst
        return tv
        }
    | ETuple es -> infer {
        let! typs = mapM inferType es
        return TCtor (KProduct, typs)
        }
    | EUnion (name, typs, cases, body) -> infer {
        // Sum types are special since they create types, first extend the user env with the new type
        let! usr = getUserEnv
        let nusr = extend usr name (List.length typs)
        do! setUserEnv nusr
        // Gather all user type usages
        let usages = List.map gatherUserTypesUsages (List.map snd cases)
        let usages = List.fold Set.union Set.empty usages
        // If any user type usages are not to types in the user environment, error
        if not <| Set.forall (checkUserTypeUsage nusr) usages then
            let bad =
                Set.filter (checkUserTypeUsage nusr >> not) usages
                |> Set.map fst
                |> String.concat ", "
            return! failure <| sprintf "Use of undeclared type constructors: %s." bad
        // Gather all free type vars in each union variant
        let ftvs = List.map (snd >> ftvType) cases
        let ftvs = List.fold Set.union Set.empty ftvs
        let udecl = Set.filter (fun s -> not <| List.contains s typs) ftvs
        // If any of them are not explicitly declared, error
        if not <| Set.isEmpty udecl then
            let fmt = udecl |> Set.map ((+) "'" ) |> String.concat ", "
            return! failure <| sprintf "Use of undeclared type variables: %s." fmt
        // Guess an inferred type
        let ret = TCtor (KSum name, List.map TVar typs)
        // Put placeholder constructors for each variant in the environment
        let! env = getTypeEnv
        let nenv = List.fold (fun acc (case, typ) ->
            extend acc case (generalize acc (TArrow (typ, ret)))) env cases 
        do! setTypeEnv nenv
        // Finally, infer the resulting type in the new environment
        return! inferType body
        }
    | EMatch (e, bs) -> infer {
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! typs = mapM (fun (pat, expr) -> infer {
            return! patternMatch pat e expr }) bs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify l r) uni
        // Compose all intermediate substitutions
        return (List.head typs)
        }
    | ERec e -> infer {
        let! t1 = inferType e
        let! tv = fresh
        do! unify (TArrow (tv, tv)) t1
        return tv
        }

// Helpers to run
let inferProgramRepl typeEnv count e =
    inferType e (typeEnv, Map.empty, Map.empty, count)
    |> fun (ty, (a,b,c,i)) ->
        match ty with
        | Ok ty -> Ok (renameFresh (applyType c ty)), i
        | Error a -> Error (sprintf "%s" a), i

let inferProgram =
    inferProgramRepl (funSchemes) 0 >> fst