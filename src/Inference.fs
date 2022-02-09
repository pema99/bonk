// Hindley-Milner type inference
// Resources:
// - https://course.ccs.neu.edu/cs4410sp19/lec_type-inference_notes.html
// - http://dev.stephendiehl.com/fun/006_hindley_milner.html#inference-monad
// - https://jgbm.github.io/eecs662f17/Notes-on-HM.html
// - Types and Programming Languages by Benjamin C. Pierce

module Inference

open Repr
open Monad
open Pretty
open Prelude

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

// Inference monad is a state monad mixed with result monad
// TODO: Put in reader for the environment. It's getting unwieldy.
type InferM<'t> = StateM<int, 't>
let infer = state
let fresh : InferM<Type> = fun c -> Ok (TVar (sprintf "_t%A" c)), c + 1
let freshName : InferM<string> = fun c -> Ok (sprintf "_t%A" c), c + 1

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
    | TBounded (ps, ty) -> Set.difference (ftvType ty) (ps |> List.map (snd >> ftvType) |> List.fold Set.union Set.empty)

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TConst _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TArrow (t1, t2) -> TArrow (applyTypeFP s t1 , applyTypeFP s t2)
        | TCtor (kind, args) -> TCtor (kind, List.map (applyTypeFP s) args)
        | TBounded (ps, ty) ->
            let r = ps |> List.collect (snd >> ftvType >> Set.toList)
            let s' = List.fold (fun acc k -> Map.remove k acc) s r
            TBounded (ps, applyTypeFP s' ty)
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

// Typeclasses
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
let supers (cls: ClassEnv) (i: string) : string list =
    match lookup cls i with
    | Some (is, its) -> is
    | None -> []

// Get the subclasses (instances) of a typeclass
let insts (cls: ClassEnv) (i: string) : Inst list =
    match lookup cls i with
    | Some (is, its) -> its
    | None -> []

// Given a predicate, which predicates must also hold by superclass relations?
let rec bySuper (cls: ClassEnv) (p: Pred) : Pred list =
    let i, t = p
    supers cls i
    |> List.collect (fun j -> bySuper cls (j, t))

// Given a predicate, which predicates must also hold by subclass relation?
let rec byInst (cls: ClassEnv) (p: Pred) : Pred list option =
    let i, t = p
    let tryInst (ps: Pred list, h) =
        if fst h = fst p then
            coerce (snd h) (snd p)
            |> Option.map (fun u -> List.map (fun (j, k) -> j, applyType u k) ps)
        else
            None
    insts cls i
    |> List.map tryInst
    |> List.tryPick id

// Do the predicates ps semantically entail p? Ie: ps_1 .. ps_n |- p
let rec entail (cls: ClassEnv) (ps: Pred list) (p: Pred) : bool =
    List.exists (List.contains p) (List.map (bySuper cls) ps) ||
    match byInst cls p with
    | Some qs -> List.forall (entail cls ps) qs
    | None -> false

// Does predicate p always hold?
let axiom (cls: ClassEnv) (p: Pred) : bool =
    entail cls [] p

// Is type 't' definitely a member of the 'klass' typeclass?
let instOf (cls: ClassEnv) (klass: string) (t: Type) : bool =
    axiom cls (klass, t)

// Unification
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec unifyList (cls: ClassEnv) (t1 : Type list) (t2 : Type list) : InferM<Substitution> = infer {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = unify cls h1 h2
        let! s2 = unifyList cls (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ -> return! failure "Unification failure"
    }

and unify (cls: ClassEnv) (t1: Type) (t2: Type) : InferM<Substitution> = infer {
    match t1, t2 with
    | a, b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TArrow (l1, r1), TArrow (l2, r2) -> return! unifyList cls [l1; r1] [l2; r2]
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        return! unifyList cls lts rts
    | TBounded (ks1, t1), t2 | t2, TBounded (ks1, t1) ->
        let! res = unify cls t1 t2
        let test = 
            List.forall (fun (klass, t) ->
                match t with
                | TVar t ->
                    lookup res t
                    |> Option.map (fun nt -> instOf cls klass nt)
                    |> Option.defaultValue false
                | _ -> true
                ) ks1
        if not test then
            return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
        return res
        // TODO: Do stuff. Maybe remove substitutions for this?
    | _ ->
        return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
    }

// Handling for user types. Map of string to type-arity of union
type UserEnv = Map<string, int>

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
    | TBounded (_, ty) -> gatherUserTypesUsages ty

// Check if a usage of a user type is valid (correct arity)
let rec checkUserTypeUsage (usr: UserEnv) (name: string, arity: int) : bool =
    match lookup usr name with
    | Some v when v = arity -> true
    | _ -> false

// Given a pattern and a type to match, recursively walk the pattern and type, gathering information along the way.
// Information gathered is in form of substitutions and changes to the typing environment (bindings). If the 'poly'
// flag is set false, bindings will not be polymorphized.
let rec gatherPatternConstraints (env: TypeEnv) (usr: UserEnv) (cls: ClassEnv) (pat: Pat) (ty: Type) (poly: bool) : InferM<Substitution * TypeEnv> = infer {
    match pat, ty with
    // Name patterns match with anything
    | PName a, ty ->
        let nt = if poly then generalize env ty else ([], ty)
        let env = extend env a nt
        return Map.empty, env
    // Constants match with anything that matches the type
    | PConstant v, ty ->
        let! s1, t1 = inferType env usr cls (ELit v)
        let! surf = unify cls ty t1
        return compose s1 surf, env
    // Tuple patterns match with same-sized tuples
    | PTuple pats, TCtor (KProduct, typs) when List.length pats = List.length typs ->
        let! env =
            foldM (fun (sub, env) (p, ty) -> infer {
                let! ns, env = gatherPatternConstraints env usr cls p ty poly
                return compose sub ns, env
            }) (Map.empty, env) (List.zip pats typs)
        return env
    // Tuple patterns match with type variables if types match
    | PTuple pats, TVar b ->
        let! tvs = mapM (fun _ -> fresh) pats
        let! subs, env = 
            foldM (fun (sub, env) (p, ty) -> infer {
                let! ns, env = gatherPatternConstraints env usr cls p ty poly
                return compose sub ns, env
            }) (Map.empty, env) (List.zip pats tvs)
        let surf = Map.ofList [b, (TCtor (KProduct, tvs))]
        return compose subs surf, env
    // Union patterns match with existant unions
    | PUnion (case, pat), ty ->
        // Check if the variant constructor exists
        match lookup env case with
        | Some sc ->
            // Instantiate it with new fresh variables
            match! instantiate sc with
            | TArrow (inp, TCtor (KSum name, oup)) ->
                // Make a fresh type variable for the pattern being bound
                let! tv = freshName
                // Gather constrains from the inner pattern matched with the fresh type variable
                let! s1, env = gatherPatternConstraints env usr cls pat (TVar tv) poly
                let env = applyEnv s1 env
                // Apply gathered constraints to the type variable to a get more concrete inner type
                let tv = applyType s1 (TVar tv)
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                let! uni1 = unify cls (TArrow (inp, TCtor (KSum name, oup))) (TArrow (tv, ty))
                // Compose intermediate substitutions and return the new environment
                return compose s1 uni1, env
            | _ -> return! failure <| sprintf "Invalid union variant %s." case
        | _ -> return! failure <| sprintf "Invalid union variant %s." case
    | a, b -> return! failure <| sprintf "Could not match pattern %A with type %A" a b
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`.
and patternMatch (env: TypeEnv) (usr: UserEnv) (cls: ClassEnv) (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Substitution * Type> = infer {
    // Infer the type of the value being bound
    let! s1, t1 = inferType env usr cls e1
    let env = applyEnv s1 env
    // Generalize it, if it is a polytype, we don't generalize the binding
    let q, t1 = generalize env t1
    let poly = not <| List.isEmpty q
    // Gather constraints (substitutions, bindings) from the pattern
    let! s2, env = gatherPatternConstraints env usr cls pat t1 poly
    let env = applyEnv s2 env
    // Infer the body/rhs of the binding under the gathered constraints
    let! s3, t3 = inferType env usr cls e2
    // Apply all constraints and propagate up
    let substf = composeAll [s1; s2; s3]
    return substf, (applyType substf t3)
    }

// Constraint gathering
and inferType (env: TypeEnv) (usr: UserEnv) (cls: ClassEnv) (e: Expr) : InferM<Substitution * Type> =
    match e with
    | ELit (LUnit _) -> just (Map.empty, tUnit)
    | ELit (LInt _) -> just (Map.empty, tInt)
    | ELit (LBool _) -> just (Map.empty, tBool)
    | ELit (LFloat _) -> just (Map.empty, tFloat)
    | ELit (LString _) -> just (Map.empty, tString)
    | ELit (LChar _) -> just (Map.empty, tChar)
    | EVar a -> infer {
        match lookup env a with
        | Some s ->
            let! inst = instantiate s
            return Map.empty, inst 
        | None ->
            return! failure <| sprintf "Use of unbound variable %A." a
        }
    | EApp (f, x) -> infer {
        let! tv = fresh
        let! s1, t1 = inferType env usr cls f
        let env = applyEnv s1 env
        let! s2, t2 = inferType env usr cls x
        let! s3 = unify cls t1 (TArrow (t2, tv))
        let substf = composeAll [s1; s2; s3]
        return substf, applyType substf tv
        }
    | ELam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh
            let env = extend env x ([], tv)
            let! s1, t1 = inferType env usr cls e
            return (s1, TArrow (applyType s1 tv, t1))
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            let! s1, env = gatherPatternConstraints env usr cls (PTuple x) (TCtor (KProduct, tvs)) false
            let env = applyEnv s1 env
            let! s2, t1 = inferType env usr cls e
            let subs = compose s1 s2
            let tvs = List.map (applyType subs) tvs
            return subs, TArrow (TCtor (KProduct, tvs), t1)
        | _->
            return! failure "Unimplemented match"
        }
    | ELet (x, e1, e2) ->
        patternMatch env usr cls x e1 e2
    | EIf (cond, tr, fl) -> infer {
        let! s1, t1 = inferType env usr cls cond
        let env = applyEnv s1 env
        let! s2, t2 = inferType env usr cls tr
        let env = applyEnv s2 env
        let! s3, t3 = inferType env usr cls fl
        let substi = composeAll [s1; s2; s3]
        let t1 = applyType substi t1
        let t2 = applyType substi t2
        let t3 = applyType substi t3
        let! s4 = unify cls t1 tBool
        let! s5 = unify cls t2 t3
        let substf = composeAll [s4; s5; substi]
        return substf, applyType substf t2
        }
    | EOp (l, op, r) -> infer {
        let! s1, t1 = inferType env usr cls l
        let! s2, t2 = inferType env usr cls r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! inst = instantiate scheme
        let! s3 = unify cls (TArrow (t1, TArrow (t2, tv))) inst
        return composeAll [s1; s2; s3], applyType s3 tv
        }
    | ETuple es -> infer {
        let! res = scanM (fun (s, _) x -> inferType (applyEnv s env) usr cls x) (Map.empty, tVoid) es
        let subs, typs = List.unzip res
        let substf = composeAll subs
        let typs = List.map (applyType substf) typs
        return substf, TCtor (KProduct, typs)
        }
    | EUnion (name, typs, cases, body) -> infer {
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
            extend acc case (generalize acc (TArrow (typ, ret)))) env cases 
        // Finally, infer the resulting type in the new environment
        return! inferType nenv usr cls body
        }
    | EMatch (e, bs) -> infer {
        let! s1, _ = inferType env usr cls e
        let env = applyEnv s1 env
        // Scan over all match branches gathering constraints from pattern matching along the way
        let! res = scanM (fun (s, _) (pat, expr) -> infer {
            let! s2, t2 = patternMatch (applyEnv s env) usr cls pat e expr
            let sub = compose s s2
            return sub, applyType sub t2 }) (Map.empty, tVoid) bs
        let subs, typs = List.unzip res
        let substi = composeAll subs
        // Apply gathered substitutions so far
        let typs = List.map (applyType substi) typs
        // Unify every match branch
        let uni = List.pairwise typs
        let! uni = mapM (fun (l, r) -> unify cls l r) uni
        // Compose all intermediate substitutions
        let substf = composeAll (substi :: uni)
        return substf, applyType substf (List.head typs)
        }
    | EClass (name, reqs, mems, rest) -> infer {
        // TODO: Take reqs into account in the bound
        let nenv = List.fold (fun acc (mem, typ) ->
            extend acc mem ([], TBounded ([name, TVar "this"], typ))) env mems
        let ncls = extend cls name (reqs, [])
        return! inferType nenv usr ncls rest
        }
    | EMember (blankets, pred, exprs, rest) -> infer {
        // Extend the class env with the new implementor
        let name, typ = pred
        let cls =
            match lookup cls name with
            | Some (reqs, insts) -> extend cls name (reqs, (blankets, pred) :: insts)
            | None -> cls
        // TODO: Semantic checking
        return! inferType env usr cls rest
        }
    | ERec e -> infer {
        let! _, t1 = inferType env usr cls e
        let! tv = fresh
        let! s2 = unify cls (TArrow (tv, tv)) t1
        return s2, applyType s2 tv
        }

// Helpers to run
let inferProgramRepl typeEnv count e =
    inferType typeEnv Map.empty Map.empty e count // TODO: Include all the envs from REPL
    |> fun (ty, i) ->
        match ty with
        | Ok (subst, ty) -> Ok (renameFresh (applyType subst ty)), i
        | Error a -> Error (sprintf "%s" a), i

let inferProgram =
    inferProgramRepl (funSchemes) 0 >> fst