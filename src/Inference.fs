// Hindley-Milner type inference
// Resources:
// - https://course.ccs.neu.edu/cs4410sp19/lec_type-inference_notes.html
// - http://dev.stephendiehl.com/fun/006_hindley_milner.html#inference-monad

module Inference

open Repr

// Inference monad is a state monad mixed with result monad
type InferM<'t> = int -> Result<'t, string> * int

type InferenceBuilder() =
  member this.Return (v: 't) : InferM<'t> =
    fun s -> Ok v, s
  member this.ReturnFrom (m: InferM<'t>) : InferM<'t> =
    m
  member this.Zero () : InferM<unit> =
    this.Return ()
  member this.Bind (m: InferM<'t>, f: 't -> InferM<'u>) : InferM<'u> =
    fun s ->
      let a, n = m s
      match a with
      | Ok v -> (f v) n
      | Error err -> Error err, n
  member this.Combine (m1: InferM<'t>, m2: InferM<'u>) : InferM<'u> =
    fun s ->
      let a, n = m1 s
      match a with
      | Ok _ -> m2 n
      | Error err -> Error err, n
  member this.Delay (f: unit -> InferM<'t>) : InferM<'t> =
    this.Bind (this.Return (), f)
  member this.FreshTypeVar() : InferM<Type> =
    fun s -> Ok (TVar (sprintf "_t%A" s)), s + 1
  member this.FreshName() : InferM<string> =
    fun s -> Ok (sprintf "_t%A" s), s + 1

let infer = InferenceBuilder()
let just = infer.Return
let fresh = infer.FreshTypeVar
let freshName = infer.FreshName
let failure err = fun s -> Error err, s
let rec mapM (f: 'a -> InferM<'b>) (t: 'a list) : InferM<'b list> = infer {
    match t with
    | h :: t ->
        let! v = f h
        let! next = mapM f t
        return v :: next
    | _ -> return []
}
let rec foldM (f: 'a -> 'b -> InferM<'a>) (acc: 'a) (t: 'b list) : InferM<'a> = infer {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let rec scanM (f: 'a -> 'b -> InferM<'a>) (acc: 'a) (t: 'b list) : InferM<'a list> = infer {
    match t with
    | h :: t ->
        let! v = f acc h 
        let! next = scanM f v t
        return v :: next 
    | _ -> return []
}

// Schemes and environments
type Scheme = string list * Type

type TypeEnv = Map<string, Scheme>
let extend env x s = Map.add x s env
let lookup env x = Map.tryFind x env
let remove env x = Map.remove x env

// Substitution
type Substitution = Map<string, Type>
let compose s1 s2 = Map.fold (fun acc k v -> Map.add k v acc) s1 s2

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

// Handling for user types
type KindEnv = Map<string, int>
// TODO: I need actual type information here, not just arity
// for pattern matching usage.

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

// Unification
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec unify (t1: Type) (t2: Type) : InferM<Substitution> = infer {
    match t1, t2 with
    | TVar a, TVar b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TCon a, TCon b when a = b -> return Map.empty
    | TArr (l1, r1), TArr (l2, r2) ->
        let! s1 = unify l1 l2
        let! s2 = unify (applyType s1 r1) (applyType s1 r2)
        return compose s2 s1
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        let! s1 =
            scanM
                (fun s (l, r) -> unify (applyType s l) (applyType s r))
                Map.empty
                (List.zip lts rts)
        return List.fold compose Map.empty s1
    | _ ->
        return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
}

// Instantiation and generalization
let instantiate (sc: Scheme) : InferM<Type> = infer {
    let (s, t) = sc
    let! ss = mapM (fun _ -> fresh()) s
    let v = List.zip s ss |> Map.ofList
    return applyType v t
}

let generalize (env: TypeEnv) (t: Type) : Scheme =
    (Set.toList <| Set.difference (ftvType t) (ftvEnv env), t)

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

// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`.
let rec patternMatch (nenv: TypeEnv) (usr: KindEnv) (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Substitution * Type> = infer {
    let! s1, t1 = inferExpr nenv usr e1
    let nenv = applyEnv s1 nenv
    match pat with
    | PName x ->
        let nt = generalize nenv t1
        let! s2, t2 = inferExpr (extend nenv x nt) usr e2
        return (compose s1 s2, t2)
    | PTuple x ->
        match t1 with
        | TCtor (KProduct _, es) when List.length x = List.length es -> // known tuple, we can infer directly
            let nts = List.map (generalize nenv) es 
            let nenv = List.fold (fun acc (name, ty) -> extend acc name ty) nenv (List.zip x nts)
            let! s2, t2 = inferExpr nenv usr e2
            return (compose s1 s2, t2)
        | TVar a -> // type variable, try to infer and surface information about the kind
            let! tvs = mapM (fun _ -> fresh()) x
            let nts = List.map (fun tv -> [], tv) tvs
            let nenv = List.fold (fun acc (name, ty) -> extend acc name ty) nenv (List.zip x nts)
            let! s2, t2 = inferExpr nenv usr e2
            let surf = (TCtor (KProduct (List.length x), tvs))
            let substf = extend (compose s1 s2) a surf
            return (substf, t2)
        | _ -> return! failure "Attempted to destructure a non-tuple with a tuple pattern."
    | PUnion (case, x) -> // union destructuring
        match t1 with
        | TCtor (KSum _, es) ->
            match lookup nenv case with
            | Some (_, TArr (inp, _)) ->
                let! ss = mapM (fun s -> unify s inp) es
                let ss = List.fold compose Map.empty ss
                let nt = generalize nenv (applyType ss inp)
                let! s2, t2 = inferExpr (extend nenv x nt) usr e2
                return (compose s1 s2, t2)
            | _ ->
                return! failure <| sprintf "Invalid sum type variant %s." case
        | TVar _ ->
            let nt = generalize nenv t1
            let! s2, t2 = inferExpr (extend nenv x nt) usr e2
            return (compose s1 s2, t2)
        | _ -> return! failure "Attempted to destructure a non-sum-type with a sum-type pattern."
    }

// Inference
and inferExpr (env: TypeEnv) (usr: KindEnv) (e: Expr) : InferM<Substitution * Type> =
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
            return (Map.empty, inst)
        | None ->
            return! failure <| sprintf "Use of unbound variable %A." a
        }
    | App (f, x) -> infer {
        let! tv = fresh()
        let! s1, t1 = inferExpr env usr f
        let! s2, t2 = inferExpr (applyEnv s1 env) usr x
        let! s3 = unify (applyType s2 t1) (TArr (t2, tv))
        return (compose s3 (compose s2 s1), applyType s3 tv)
        }
    | Lam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh()
            let nenv = extend env x ([], tv)
            let! s1, t1 = inferExpr nenv usr e
            return (s1, TArr (applyType s1 tv, t1))
        | PTuple x -> 
            let! tvs = mapM (fun _ -> fresh()) x
            let nenv = List.fold (fun acc (s, tv) -> extend acc s ([], tv)) env (List.zip x tvs)
            let! s1, t1 = inferExpr nenv usr e
            let tvs = List.map (applyType s1) tvs
            return (s1, TArr (TCtor (KProduct (List.length tvs), tvs), t1))
        | PUnion (case, x) ->
            match lookup env case with
            | Some (_, TArr (_, union)) -> return! failure "Unimplemented match"
            | _ -> return! failure <| sprintf "Couldn't find sum type variant %s" case
        }
    | Let (x, e1, e2) ->
        patternMatch env usr x e1 e2
    | If (cond, tr, fl) -> infer {
        let! s1, t1 = inferExpr env usr cond
        let env = applyEnv s1 env
        let! s2, t2 = inferExpr env usr tr
        let env = applyEnv s1 env
        let! s3, t3 = inferExpr env usr fl
        let substi = compose s3 (compose s2 s1)
        let t1 = applyType substi t1
        let t2 = applyType substi t2
        let t3 = applyType substi t3
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        let substf = compose s5 (compose s4 substi)
        return (substf, applyType substf t2)
        }
    | Op (l, op, r) -> infer {
        let! s1, t1 = inferExpr env usr l
        let! s2, t2 = inferExpr env usr r
        let! tv = fresh()
        let scheme = Map.find op ops
        let! inst = instantiate scheme
        let! s3 = unify (TArr (t1, TArr (t2, tv))) inst
        return (compose s1 (compose s2 s3), applyType s3 tv)
        }
    | Tup es -> infer {
        let! s1 = scanM (fun (s, _) x -> inferExpr (applyEnv s env) usr x) (Map.empty, tVoid) es
        let subs, typs = s1 |> List.unzip
        let substf = List.fold compose Map.empty subs
        let typs = List.map (applyType substf) typs
        return (substf, TCtor (KProduct (List.length es), typs))
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
        let! s1, t1 = inferExpr nenv usr body
        return (s1, t1)
        }
    | Match (e, bs) -> infer {
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! s1, _ = inferExpr env usr e
        let nenv = applyEnv s1 env
        let! s2 = scanM (fun (s, _) (pat, expr) -> patternMatch (applyEnv s nenv) usr pat e expr) (s1, tVoid) bs
        let subs, typs = s2 |> List.unzip
        // Compose all gathered constraints
        let subst = List.fold compose Map.empty subs
        let typs = List.map (applyType subst) typs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify l r) uni
        // Compose all intermediate constraints
        let substf = List.fold compose Map.empty uni
        return (compose subst substf, applyType substf (List.head typs))
        }
    | Rec e -> infer {
        let! _, t1 = inferExpr env usr e
        let! tv = fresh()
        let! s2 = unify (TArr (tv, tv)) t1
        return (s2, applyType s2 tv)
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

let inferProgram e =
    inferExpr Map.empty Map.empty e 0
    |> fst
    |> Result.map (snd >> renameFresh)