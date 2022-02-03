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

// Inference monad is a RWS monad mixed with result monad
type StateM<'s, 't> = 's -> Result<'t, string> * 's
type InferM<'t> = StateM<TypeEnv * Constraint list * int, 't>

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
        fun (a,b,c) -> Ok (TVar (sprintf "_t%A" c)), (a, b, c + 1)
    member this.FreshName() : InferM<string> =
        fun (a,b,c) -> Ok (sprintf "_t%A" c), (a, b, c + 1)
    // Writer monad
    member this.Tell(con: Constraint) : InferM<unit> =
        fun (a,b,c) -> Ok (), (a, con :: b, c)
    // Reader monad
    member this.Ask() : InferM<TypeEnv> =
        fun (a,b,c) -> Ok a, (a, b, c) 
    member this.Local(f: TypeEnv -> TypeEnv, m: InferM<'a>) : InferM<'a> =
        fun (a,b,c) -> m (f a, b, c)

let state = StateBuilder()
let infer = state
let solve = state
let just = state.Return
let fresh = state.FreshTypeVar
let freshName = state.FreshName
let tell = state.Tell
let ask = state.Ask
let local f m = state.Local (f, m)
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

let rec constrain (t1: Type) (t2: Type) : InferM<unit> = tell (t1, t2)

let rec inEnv (n: string) (sc: Scheme) (m: InferM<'a>) : InferM<'a> = infer {
    let scopeTo e = extend (Map.remove n e) n sc
    return! local scopeTo m
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
let rec patternMatch (usr: KindEnv) (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Type> = infer {
    let! t1 = inferExpr usr e1
    match pat with
    | PName x ->
        let! nenv = ask()
        let nt = generalize nenv t1
        return! inEnv x nt (inferExpr usr e2)
    | PTuple x ->
        match t1 with
        | TCtor (KProduct _, es) when List.length x = List.length es -> // known tuple, we can infer directly
            let! nenv = ask()
            let nts = List.map (generalize nenv) es 
            let nenv env = List.fold (fun acc (name, ty) -> extend acc name ty) env (List.zip x nts)
            return! local nenv (inferExpr usr e2)
        | TVar a -> // type variable, try to infer and surface information about the kind
            let! tvs = mapM (fun _ -> fresh()) x
            let nts = List.map (fun tv -> [], tv) tvs
            let nenv env = List.fold (fun acc (name, ty) -> extend acc name ty) env (List.zip x nts)
            let! t2 = local nenv (inferExpr usr e2)
            let surf = (TCtor (KProduct (List.length x), tvs))
            do! constrain (TVar a) surf
            return t2
        | _ -> return! failure "Attempted to destructure a non-tuple with a tuple pattern."
    | PUnion (case, x) -> // union destructuring
        match t1 with
        | TCtor (KSum _, es) ->
            let! nenv = ask()
            match lookup nenv case with
            | Some (_, TArr (inp, _)) ->
                let! _ = mapM (fun s -> constrain s inp) es
                let nt = generalize nenv inp
                return! inEnv x nt (inferExpr usr e2)
            | _ ->
                return! failure <| sprintf "Invalid sum type variant %s." case
        | TVar _ ->
            let! nenv = ask()
            let nt = generalize nenv t1
            return! inEnv x nt (inferExpr usr e2)
        | _ -> return! failure "Attempted to destructure a non-sum-type with a sum-type pattern."
    }

// Constraint gathering
and inferExpr (usr: KindEnv) (e: Expr) : InferM<Type> =
    match e with
    | Lit (LUnit _) -> just tUnit
    | Lit (LInt _) -> just tInt
    | Lit (LBool _) -> just tBool 
    | Lit (LFloat _) -> just tFloat 
    | Lit (LString _) -> just tString
    | Var a -> infer {
        let! env = ask()
        match lookup env a with
        | Some s ->
            let! inst = instantiate s
            return inst
        | None ->
            return! failure <| sprintf "Use of unbound variable %A." a
        }
    | App (f, x) -> infer {
        let! tv = fresh()
        let! t1 = inferExpr usr f
        let! t2 = inferExpr usr x
        do! constrain t1 (TArr (t2, tv))
        return tv
        }
    | Lam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh()
            let! t = inEnv x ([], tv) (inferExpr usr e)
            return (TArr (tv, t))
        | PTuple x -> 
            let! tvs = mapM (fun _ -> fresh()) x
            let nenv env = List.fold (fun acc (s, tv) -> extend acc s ([], tv)) env (List.zip x tvs)
            let! t1 = local nenv (inferExpr usr e)
            return TArr (TCtor (KProduct (List.length tvs), tvs), t1)
        | PUnion (case, x) ->
            let! env = ask()
            match lookup env case with
            | Some (_, TArr (_, union)) -> return! failure "Unimplemented match"
            | _ -> return! failure <| sprintf "Couldn't find sum type variant %s" case
        }
    | Let (x, e1, e2) ->
        patternMatch usr x e1 e2
    | If (cond, tr, fl) -> infer {
        let! t1 = inferExpr usr cond
        let! t2 = inferExpr usr tr
        let! t3 = inferExpr usr fl
        do! constrain t1 tBool
        do! constrain t2 t3
        return t2
        }
    | Op (l, op, r) -> infer {
        let! t1 = inferExpr usr l
        let! t2 = inferExpr usr r
        let! tv = fresh()
        let scheme = Map.find op ops
        let! inst = instantiate scheme
        do! constrain (TArr (t1, TArr (t2, tv))) inst
        return tv
        }
    | Tup es -> infer {
        let! typs = mapM (fun x -> inferExpr usr x) es
        return TCtor (KProduct (List.length es), typs)
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
        let nenv env = List.fold (fun acc (case, typ) ->
            extend acc case (generalize acc (TArr (typ, ret)))) env cases 
        // Finally, infer the resulting type in the new environment
        return! local nenv (inferExpr usr body)
        }
    | Match (e, bs) -> infer { // TODO: This is definitely wrong
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! typs = mapM (fun (pat, expr) -> patternMatch usr pat e expr) bs
        // Unify every match branch
        let uni = List.pairwise typs
        let! _ = mapM (fun (l, r) -> constrain l r) uni
        return List.head typs
        }
    | Rec e -> infer {
        let! t1 = inferExpr usr e
        let! tv = fresh()
        do! constrain (TArr (tv, tv)) t1
        return tv
        }

// Constraint solving, solver monad is just a state monad over gathered substitutions
type SolveM<'t> = StateM<Substitution, 't>

let rec unifyList (t1 : Type list) (t2 : Type list) : SolveM<Substitution> = solve {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = unify h1 h2
        let! s2 = unifyList (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ -> return! failure "Unification failure"
    }

and unify (t1: Type) (t2: Type) : SolveM<Substitution> = solve {
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

let rec solver (su: Substitution, cs: Constraint list) : SolveM<Substitution> = solve {
    match cs with
    | [] -> return su
    | (t1, t2) :: ta ->
        let! s1 = unify t1 t2
        return! solver (compose s1 su, List.map (applyConstraint s1) ta)
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
    inferExpr Map.empty e (typeEnv, [], count)
    |> fun (ty, (_, cs, i)) ->
        let subst = fst <| (solver (Map.empty, cs)) Map.empty
        match ty, subst with
        | Ok ty, Ok subst -> Ok (renameFresh (applyType subst ty)), i
        | Error a, Error b -> Error (sprintf "%s %s" a b), i
        | Error a, _ | _, Error a -> Error a, i

let inferProgram =
    inferProgramRepl Map.empty 0 >> fst