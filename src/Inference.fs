// Hindley-Milner type inference
// Resources:
// - https://course.ccs.neu.edu/cs4410sp19/lec_type-inference_notes.html
// - http://dev.stephendiehl.com/fun/006_hindley_milner.html#inference-monad

module Inference

open Repr

// Schemes, constraints and environments
type Constraint = Type * Type

type Scheme = string list * Type

type TypeEnv = Map<string, Scheme>
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env

// Substitution
type Substitution = Map<string, Type>
let compose s1 s2 = Map.fold (fun acc k v -> Map.add k v acc) s1 s2
let composeAll lst = List.fold compose Map.empty lst

// Inference monad is a RWS monad mixed with result monad
type StateM<'s, 't> = 's -> Result<'t, string> * 's
type InferM<'t> = StateM<int, 't>

type StateBuilder() =
    member this.Return (v: 't) : StateM<'s, 't> =
        fun s -> Ok v, s
    member this.ReturnFrom (m: StateM<'s, 't>) : StateM<'s, 't> =
        m
    member this.Zero () : StateM<'s, unit> =
        this.Return ()
    member this.Bind (m: StateM<'s, 't>, f: 't -> StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m s
            match a with
            | Ok v -> (f v) n
            | Error err -> Error err, n
    member this.Combine (m1: StateM<'s, 't>, m2: StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m1 s
            match a with
            | Ok _ -> m2 n
            | Error err -> Error err, n
    member this.Delay (f: unit -> StateM<'s, 't>) : StateM<'s, 't> =
        this.Bind (this.Return (), f)
    // Freshname monad
    member this.FreshTypeVar() : InferM<Type> =
        fun c -> Ok (TVar (sprintf "_t%A" c)), c + 1
    member this.FreshName() : InferM<string> =
        fun c -> Ok (sprintf "_t%A" c), c + 1

let state = StateBuilder()
let infer = state
let solve = state
let just = state.Return
let fresh = state.FreshTypeVar
let freshName = state.FreshName
let failure err = fun s -> Error err, s
let rec mapM (f: 'a -> StateM<'s, 'b>) (t: 'a list) : StateM<'s, 'b list> = state {
    match t with
    | h :: t ->
        let! v = f h
        let! next = mapM f t
        return v :: next
    | _ -> return []
}
let rec foldM (f: 'a -> 'b -> InferM<'a>) (acc: 'a) (t: 'b list) : InferM<'a> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let rec scanM (f: 'a -> 'b -> InferM<'a>) (acc: 'a) (t: 'b list) : InferM<'a list> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        let! next = scanM f v t
        return v :: next 
    | _ -> return []
}

// Substitution application
let rec fixedPoint f s t =
    let subst = f s t
    if subst = t then subst
    else fixedPoint f s subst

let rec ftvType (t: Type) : string Set =
    match t with
    | TCon _ -> Set.empty
    | TVar a -> Set.singleton a
    | TArr (t1, t2) -> Set.union (ftvType t1) (ftvType t2)
    | TCtor (_, args) -> args |> List.map ftvType |> List.fold Set.union Set.empty

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TCon _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TArr (t1, t2) -> TArr (applyTypeFP s t1 , applyTypeFP s t2)
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

let ftvConstraint (t1: Type, t2: Type) : Set<string> =
    Set.union (ftvType t1) (ftvType t2)

let applyConstraint =
    let applyConstraintFP (s: Substitution) (t1: Type, t2: Type) : Constraint =
        applyType s t1, applyType s t2
    fixedPoint applyConstraintFP

// Type schemes for built in operators
let ops = Map.ofList [
    Plus, (["a"], TArr (TVar "a", TArr (TVar "a", TVar "a")))
    Minus, (["a"], TArr (TVar "a", TArr (TVar "a", TVar "a")))
    Star, (["a"], TArr (TVar "a", TArr (TVar "a", TVar "a")))
    Slash, (["a"], TArr (TVar "a", TArr (TVar "a", TVar "a")))
    Equal, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    NotEq, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    GreaterEq, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    LessEq, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    Greater, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    Less, (["a"], TArr (TVar "a", TArr (TVar "a", tBool)))
    And, ([], TArr (tBool, TArr (tBool, tBool)))
    Or, ([], TArr (tBool, TArr (tBool, tBool)))
    ]

// Instantiate a monotype from a polytype
let instantiate (sc: Scheme) : InferM<Type> = infer {
    let (s, t) = sc
    let! ss = mapM (fun _ -> fresh()) s
    let v = List.zip s ss |> Map.ofList
    return applyType v t
}

// Generalize a monotype to a polytype
let generalize (env: TypeEnv) (t: Type) : Scheme =
    (Set.toList <| Set.difference (ftvType t) (ftvEnv env), t)

// Unification
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec unifyList (t1 : Type list) (t2 : Type list) : InferM<Substitution> = solve {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = unify h1 h2
        let! s2 = unifyList (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ -> return! failure "Unification failure"
    }

and unify (t1: Type) (t2: Type) : InferM<Substitution> = solve {
    match t1, t2 with
    | a, b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TArr (l1, r1), TArr (l2, r2) -> return! unifyList [l1; r1] [l2; r2]
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        return! unifyList lts rts
    | _ ->
        return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
    }

// Handling for user types
type KindEnv = Map<string, int>
// TODO: I need actual type information here, not just arity for pattern matching.

// Gather all usages of user types in a type
let rec gatherUserTypesUsages (t: Type) : Set<string * int> =
    match t with
    | TVar _ | TCon _ -> Set.empty
    | TArr (l, r) -> Set.union (gatherUserTypesUsages l) (gatherUserTypesUsages r)
    | TCtor (kind, lts) ->
        let inner = List.map gatherUserTypesUsages lts
        let inner = List.fold Set.union Set.empty inner
        match kind with
        | KSum name -> Set.add (name, List.length lts) inner
        | _ -> inner

// Check if a usage of a user type is valid (correct arity)
let rec checkUserTypeUsage (usr: KindEnv) (name: string, arity: int) : bool =
    match lookup usr name with
    | Some v when v = arity -> true
    | _ -> false

// Given a pattern and a type to match, recursively walk the pattern and type, gathering information along the way.
// Information gathered is in form of substitutions and changes to the typing environment (bindings). If the 'poly'
// flag is set false, bindings will not be polymorphized.
let rec gatherPatternConstraints (env: TypeEnv) (usr: KindEnv) (pat: Pat) (ty: Type) (poly: bool) : InferM<Substitution * TypeEnv> = infer {
    match pat, ty with
    // Name patterns match with anything
    | PName a, ty ->
        let nt = if poly then generalize env ty else ([], ty)
        let env = extend env a nt
        return Map.empty, env
    // Constants match with anything that matches the type
    | PConstant v, ty ->
        let! s1, t1 = inferType env usr (Lit v)
        let! surf = unify ty t1
        return compose s1 surf, env
    // Tuple patterns match with same-sized tuples
    | PTuple pats, TCtor (KProduct arity, typs) when List.length pats = List.length typs ->
        let! env =
            foldM (fun (sub, env) (p, ty) -> infer {
                let! ns, env = gatherPatternConstraints env usr p ty poly
                return compose sub ns, env
            }) (Map.empty, env) (List.zip pats typs)
        return env
    // Tuple patterns match with type variables if types match
    | PTuple pats, TVar b ->
        let! tvs = mapM (fun _ -> fresh()) pats
        let! subs, env = 
            foldM (fun (sub, env) (p, ty) -> infer {
                let! ns, env = gatherPatternConstraints env usr p ty poly
                return compose sub ns, env
            }) (Map.empty, env) (List.zip pats tvs)
        let surf = Map.ofList [b, (TCtor (KProduct (List.length pats), tvs))]
        return compose subs surf, env
    // Union patterns match with existant unions
    | PUnion (case, pat), ty ->
        // Check if the variant constructor exists
        match lookup env case with
        | Some sc ->
            // Instantiate it with new fresh variables
            match! instantiate sc with
            | TArr (inp, TCtor (KSum name, oup)) ->
                // Make a fresh type variable for the pattern being bound
                let! tv = freshName()
                // Gather constrains from the inner pattern matched with the fresh type variable
                let! s1, env = gatherPatternConstraints env usr pat (TVar tv) poly
                let env = applyEnv s1 env
                // Apply gathered constraints to the type variable to a get more concrete inner type
                let tv = applyType s1 (TVar tv)
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                let! uni1 = unify (TArr (inp, TCtor (KSum name, oup))) (TArr (tv, ty))
                // Compose intermediate substitutions and return the new environment
                return compose s1 uni1, env
            | _ -> return! failure <| sprintf "Invalid union variant %s." case
        | _ -> return! failure <| sprintf "Invalid union variant %s." case
    | a, b -> return! failure <| sprintf "Could not match pattern %A with type %A" a b
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`.
and patternMatch (env: TypeEnv) (usr: KindEnv) (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Substitution * Type> = infer {
    // Infer the type of the value being bound
    let! s1, t1 = inferType env usr e1
    let env = applyEnv s1 env
    // Generalize it, if it is a polytype, we don't generalize the binding
    let q, t1 = generalize env t1
    let poly = not <| List.isEmpty q
    // Gather constraints (substitutions, bindings) from the pattern
    let! s2, env = gatherPatternConstraints env usr pat t1 poly
    let env = applyEnv s2 env
    // Infer the body/rhs of the binding under the gathered constraints
    let! s3, t3 = inferType env usr e2
    // Apply all constraints and propagate up
    let substf = composeAll [s1; s2; s3]
    return substf, (applyType substf t3)
    }

// Constraint gathering
and inferType (env: TypeEnv) (usr: KindEnv) (e: Expr) : InferM<Substitution * Type> =
    match e with
    | Lit (LUnit _) -> just (Map.empty, tUnit)
    | Lit (LInt _) -> just (Map.empty, tInt)
    | Lit (LBool _) -> just (Map.empty, tBool)
    | Lit (LFloat _) -> just (Map.empty, tFloat)
    | Lit (LString _) -> just (Map.empty, tString)
    | Var a -> infer {
        match lookup env a with
        | Some s ->
            let! inst = instantiate s
            return Map.empty, inst 
        | None ->
            return! failure <| sprintf "Use of unbound variable %A." a
        }
    | App (f, x) -> infer {
        let! tv = fresh()
        let! s1, t1 = inferType env usr f
        let env = applyEnv s1 env
        let! s2, t2 = inferType env usr x
        let! s3 = unify t1 (TArr (t2, tv))
        let substf = composeAll [s1; s2; s3]
        return substf, applyType substf tv
        }
    | Lam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh()
            let env = extend env x ([], tv)
            let! s1, t1 = inferType env usr e
            return (s1, TArr (applyType s1 tv, t1))
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh()) x
            let! s1, env = gatherPatternConstraints env usr (PTuple x) (TCtor (KProduct (List.length tvs), tvs)) false
            let env = applyEnv s1 env
            let! s2, t1 = inferType env usr e
            let subs = compose s1 s2
            let tvs = List.map (applyType subs) tvs
            return subs, TArr (TCtor (KProduct (List.length tvs), tvs), t1)
        | _->
            return! failure "Unimplemented match"
        }
    | Let (x, e1, e2) ->
        patternMatch env usr x e1 e2
    | If (cond, tr, fl) -> infer {
        let! s1, t1 = inferType env usr cond
        let env = applyEnv s1 env
        let! s2, t2 = inferType env usr tr
        let env = applyEnv s2 env
        let! s3, t3 = inferType env usr fl
        let substi = composeAll [s1; s2; s3]
        let t1 = applyType substi t1
        let t2 = applyType substi t2
        let t3 = applyType substi t3
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        let substf = composeAll [s4; s5; substi]
        return substf, applyType substf t2
        }
    | Op (l, op, r) -> infer {
        let! s1, t1 = inferType env usr l
        let! s2, t2 = inferType env usr r
        let! tv = fresh()
        let scheme = Map.find op ops
        let! inst = instantiate scheme
        let! s3 = unify (TArr (t1, TArr (t2, tv))) inst
        return composeAll [s1; s2; s3], applyType s3 tv
        }
    | Tup es -> infer {
        let! res = scanM (fun (s, _) x -> inferType (applyEnv s env) usr x) (Map.empty, tVoid) es
        let subs, typs = List.unzip res
        let substf = composeAll subs
        let typs = List.map (applyType substf) typs
        return substf, TCtor (KProduct (List.length es), typs)
        }
    | Sum (name, typs, cases, body) -> infer {
        // Sum types are special since they create types, first extend the user env with the new type
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
        let nenv = List.fold (fun acc (case, typ) ->
            extend acc case (generalize acc (TArr (typ, ret)))) env cases 
        // Finally, infer the resulting type in the new environment
        return! inferType nenv usr body
        }
    | Match (e, bs) -> infer {
        let! s1, _ = inferType env usr e
        let env = applyEnv s1 env
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! res = scanM (fun (s, _) (pat, expr) -> infer {
            let! s2, t2 = patternMatch (applyEnv s env) usr pat e expr
            let sub = compose s s2
            return sub, applyType sub t2 }) (Map.empty, tVoid) bs
        let subs, typs = List.unzip res
        let substi = composeAll subs
        // Apply gathered substitutions so far
        let typs = List.map (applyType substi) typs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify l r) uni
        // Compose all intermediate substitutions
        let substf = composeAll (substi :: uni)
        return substf, applyType substf (List.head typs)
        }
    | Rec e -> infer {
        let! _, t1 = inferType env usr e
        let! tv = fresh()
        let! s2 = unify (TArr (tv, tv)) t1
        return s2, applyType s2 tv
        }

// Pretty naming
let prettyTypeName (i: int) : string =
    if i < 26 then string <| 'a' + char i
    else sprintf "t%A" i

let renameFresh (t: Type) : Type =
    let rec cont t subst count =
        match t with
        | TCon _ -> t, subst, count
        | TArr (l, r) ->
            let (r1, subst1, count1) = cont l subst count
            let (r2, subst2, count2) = cont r subst1 count1
            TArr (r1, r2), subst2, count2
        | TVar a ->
            match lookup subst a with
            | Some v -> TVar v, subst, count
            | None ->
                let name = prettyTypeName count
                let nt = TVar name
                nt, extend subst a name, count + 1
        | TCtor (kind, args) ->
            let lst =
                args
                |> List.scan (fun (_, subst, count) x -> cont x subst count) (tVoid, subst, count)
                |> List.tail
            let args, substs, counts = List.unzip3 lst
            TCtor (kind, args),
            List.tryLast substs |> Option.defaultValue subst,
            List.tryLast counts |> Option.defaultValue count
    let (res, _, _) = cont t Map.empty 0
    res

let rec prettyType (t: Type) : string =
    match t with
    | TCon v -> v
    | TVar v -> sprintf "'%s" v
    | TArr (l, r) -> sprintf "(%s -> %s)" (prettyType l) (prettyType r) 
    | TCtor (kind, args) ->
        match kind with
        | KProduct _ ->
            args
            |> List.map prettyType
            |> List.toArray
            |> String.concat " * "
            |> sprintf "(%s)"
        | KSum name ->
            let fmt =
                args
                |> List.map prettyType
                |> List.toArray
                |> String.concat ", "
            if fmt = "" then name
            else sprintf "%s<%s>" name fmt
        | _ -> "<Invalid>"    

// Helpers to run
let inferProgramRepl typeEnv count e =
    inferType typeEnv Map.empty e count
    |> fun (ty, i) ->
        match ty with
        | Ok (subst, ty) -> Ok (renameFresh (applyType subst ty)), i
        | Error a -> Error (sprintf "%s" a), i

let inferProgram =
    inferProgramRepl Map.empty 0 >> fst