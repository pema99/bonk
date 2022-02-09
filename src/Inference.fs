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

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TConst _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TArrow (t1, t2) -> TArrow (applyTypeFP s t1 , applyTypeFP s t2)
        | TCtor (kind, args) -> TCtor (kind, List.map (applyTypeFP s) args)
    fixedPoint applyTypeFP

let rec ftvPred (p: Pred) : string Set =
    p |> snd |> ftvType

let rec applyPred (s: Substitution) (p: Pred) : Pred =
    (fst p, applyType s (snd p))

let rec ftvInst (q: Qual<Pred>) : string Set =
    let a, b = q
    List.map (ftvPred) a |> List.fold Set.union Set.empty |> Set.union (ftvPred b)

let rec applyInst (s: Substitution) (q: Qual<Pred>) : Qual<Pred> =
    let a, b = q
    List.map (applyPred s) a, applyPred s b

//let rec ftvQualType (q: Qual<Type>) : string Set =
//    let a, b = q
//    List.map (ftvPred) a |> List.fold Set.union Set.empty |> Set.union (ftvType b)

//let rec applyQualType (s: Substitution) (q: Qual<Type>) : Qual<Type> =
//    let a, b = q
//    List.map (applyPred s) a, applyType s b

let ftvScheme (sc: Scheme) : string Set =
    let a, t = sc
    Set.difference (ftvType t) (a |> List.map ftvPred |> List.fold Set.union Set.empty) 

let applyScheme =
    let rec applySchemeFP (s: Substitution) (sc: Scheme) : Scheme =
        let a, t = sc
        let r = a |> List.collect (ftvPred >> Set.toList)
        let s' = List.fold (fun acc k -> Map.remove k acc) s r
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
let instantiate (sc: Scheme) : InferM<Scheme> = infer {
    let tvs = sc |> fst |> List.map ftvPred |> List.fold Set.union Set.empty |> Set.toList 
    let! ntvs = mapM (fun _ -> fresh) tvs
    let subs = List.zip tvs ntvs |> Map.ofList
    return applyScheme subs sc // TODO: Is this right???
}

// Generalize a monotype to a polytype
let generalize (env: TypeEnv) (t: Type) : Scheme =
    let res = Set.toList <| Set.difference (ftvType t) (ftvEnv env)
    (res |> List.map (fun s -> ("Top", TVar s)), t)

// Unification
let occurs (s: string) (t: Type) : bool =
    Set.exists ((=) s) (ftvType t)

let rec unifyList (t1 : Type list) (t2 : Type list) : InferM<Substitution> = infer {
    match t1, t2 with
    | [], [] -> return Map.empty
    | h1::ta1, h2::ta2 -> 
        let! s1 = unify h1 h2
        let! s2 = unifyList (List.map (applyType s1) ta1) (List.map (applyType s1) ta2)
        return compose s2 s1
    | _ -> return! failure "Unification failure"
    }

and unify (t1: Type) (t2: Type) : InferM<Substitution> = infer {
    match t1, t2 with
    | a, b when a = b -> return Map.empty
    | TVar a, b when not (occurs a b) -> return Map.ofList [(a, b)]
    | a, TVar b when not (occurs b a) -> return Map.ofList [(b, a)]
    | TArrow (l1, r1), TArrow (l2, r2) -> return! unifyList [l1; r1] [l2; r2]
    | TCtor (kind1, lts), TCtor (kind2, rts) when kind1 = kind2 && List.length lts = List.length rts ->
        return! unifyList lts rts
    | _ ->
        return! failure <| sprintf "Failed to unify types %A and %A." t1 t2
    }

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

// Typeclasses
let super (cls: ClassEnv) (i: string) : string list =
    match lookup cls i with
    | Some (is, _) -> is
    | _ -> []

let insts (cls: ClassEnv) (i: string) : Inst list =
    match lookup cls i with
    | Some (_, its) -> its
    | _ -> []

let rec bySuper (cls: ClassEnv) (p: Pred) : Pred list =
    let i, t = p
    let res =
        super cls i
        |> List.collect (fun ip -> bySuper cls (ip, t))
    p :: res

let rec byInst (cls: ClassEnv) (p: Pred) : Pred list option =
    let i, t = p
    let tryInst (ps, h) =
        if h = p then
            coerce (snd h) (snd p)
            |> Option.map (fun u -> List.map (applyPred u) ps)
        else
            None
    insts cls i
    |> List.map tryInst
    |> List.tryPick id

let rec entail (cls: ClassEnv) (ps: Pred list) (p: Pred) : bool =
    List.exists (List.contains p) (List.map (bySuper cls) ps) ||
    match byInst cls p with
    | Some qs -> List.forall (entail cls ps) qs
    | None -> false

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
        let! s1, (_, t1) = inferType env usr cls (ELit v) // TODO: Handle
        let! surf = unify ty t1
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
            | (_, TArrow (inp, TCtor (KSum name, oup))) ->
                // Make a fresh type variable for the pattern being bound
                let! tv = freshName
                // Gather constrains from the inner pattern matched with the fresh type variable
                let! s1, env = gatherPatternConstraints env usr cls pat (TVar tv) poly
                let env = applyEnv s1 env
                // Apply gathered constraints to the type variable to a get more concrete inner type
                let tv = applyType s1 (TVar tv)
                // Unify the variant constructor with an arrow type from the inner type to the type being matched on
                // for example, unify `'a -> Option<'a>` with `typeof(x) -> typeof(h)` in `let Some x = h`
                let! uni1 = unify (TArrow (inp, TCtor (KSum name, oup))) (TArrow (tv, ty))
                // Compose intermediate substitutions and return the new environment
                return compose s1 uni1, env
            | _ -> return! failure <| sprintf "Invalid union variant %s." case
        | _ -> return! failure <| sprintf "Invalid union variant %s." case
    | a, b -> return! failure <| sprintf "Could not match pattern %A with type %A" a b
    }


// Given an environment, a pattern, and 2 expressions being related by the pattern, attempt to
// infer the type of expression 2. Example are let bindings `let pat = e1 in e2` and match
// expressions `match e1 with pat -> e2`.
and patternMatch (env: TypeEnv) (usr: UserEnv) (cls: ClassEnv) (pat: Pat) (e1: Expr) (e2: Expr) : InferM<Substitution * Scheme> = infer {
    // Infer the type of the value being bound
    let! s1, (p1, t1) = inferType env usr cls e1
    let env = applyEnv s1 env
    // If it is a polytype, we don't generalize the binding // TODO: Check this? I generalized before
    let poly = not <| List.isEmpty p1
    // Gather constraints (substitutions, bindings) from the pattern
    let! s2, env = gatherPatternConstraints env usr cls pat t1 poly
    let env = applyEnv s2 env
    // Infer the body/rhs of the binding under the gathered constraints
    let! s3, (p3, t3) = inferType env usr cls e2
    // Apply all constraints and propagate up
    let substf = composeAll [s1; s2; s3]
    return substf, (p1 @ p3, (applyType substf t3))
    }

// Constraint gathering
and inferType (env: TypeEnv) (usr: UserEnv) (cls: ClassEnv) (e: Expr) : InferM<Substitution * Scheme> =
    match e with
    | ELit (LUnit _) -> just (Map.empty, sUnit)
    | ELit (LInt _) -> just (Map.empty, sInt)
    | ELit (LBool _) -> just (Map.empty, sBool)
    | ELit (LFloat _) -> just (Map.empty, sFloat)
    | ELit (LString _) -> just (Map.empty, sString)
    | ELit (LChar _) -> just (Map.empty, sChar)
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
        let! s1, (p1, t1) = inferType env usr cls f
        let env = applyEnv s1 env
        let! s2, (p2, t2) = inferType env usr cls x
        let! s3 = unify t1 (TArrow (t2, tv))
        let substf = composeAll [s1; s2; s3]
        return substf, (p1 @ p2, applyType substf tv)
        }
    | ELam (x, e) -> infer {
        match x with
        | PName x ->
            let! tv = fresh
            let env = extend env x ([], tv)
            let! s1, (p1, t1) = inferType env usr cls e
            return s1, (p1, TArrow (applyType s1 tv, t1))
        | PTuple x ->
            let! tvs = mapM (fun _ -> fresh) x
            let! s1, env = gatherPatternConstraints env usr cls (PTuple x) (TCtor (KProduct, tvs)) false
            let env = applyEnv s1 env
            let! s2, (p1, t1) = inferType env usr cls e
            let subs = compose s1 s2
            let tvs = List.map (applyType subs) tvs
            return subs, (p1, TArrow (TCtor (KProduct, tvs), t1))
        | _->
            return! failure "Unimplemented match"
        }
    | ELet (x, e1, e2) ->
        patternMatch env usr cls x e1 e2
    | EIf (cond, tr, fl) -> infer {
        let! s1, (p1, t1) = inferType env usr cls cond
        let env = applyEnv s1 env
        let! s2, (p2, t2) = inferType env usr cls tr
        let env = applyEnv s2 env
        let! s3, (p3, t3) = inferType env usr cls fl
        let substi = composeAll [s1; s2; s3]
        let t1 = applyType substi t1
        let t2 = applyType substi t2
        let t3 = applyType substi t3
        let! s4 = unify t1 tBool
        let! s5 = unify t2 t3
        let substf = composeAll [s4; s5; substi]
        return substf, (p1 @ p2 @ p3, applyType substf t2)
        }
    | EOp (l, op, r) -> infer {
        let! s1, (p1, t1) = inferType env usr cls l
        let! s2, (p2, t2) = inferType env usr cls r
        let! tv = fresh
        let scheme = Map.find op opSchemes
        let! (p3, inst) = instantiate scheme
        let! s3 = unify (TArrow (t1, TArrow (t2, tv))) inst
        return composeAll [s1; s2; s3], (p1 @ p2 @ p3, applyType s3 tv)
        }
    | ETuple es -> infer {
        let! res = scanM (fun (s, _) x -> inferType (applyEnv s env) usr cls x) (Map.empty, sVoid) es
        let subs, scs = List.unzip res
        let substf = composeAll subs
        let scs = List.map (applyScheme substf) scs
        let ps = List.unzip scs |> fst |> List.concat
        let typs = List.unzip scs |> snd
        return substf, (ps, TCtor (KProduct, typs))
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
            return sub, applyScheme sub t2 }) (Map.empty, sVoid) bs
        let subs, scs = List.unzip res
        let substi = composeAll subs
        // Apply gathered substitutions so far
        let scs = List.map (applyScheme substi) scs
        // Unify every match branch
        let uni = List.pairwise scs
        printfn "%A" (List.map snd scs)
        let! uni = mapM (fun (l, r) -> unify l r) (List.map (fun (a, b) -> snd a, snd b) uni) // TODO: Sus
        // Compose all intermediate substitutions
        let substf = composeAll (substi :: uni)
        return substf, applyScheme substf (List.head scs)
        }
    | EClass (name, mems, rest) -> infer {
        (*let cls = extend cls name ([], [])
        let nenv = List.fold (fun acc (mem, typ) ->
            extend acc mem ([], TBounded ([name], typ))) env mems
        return! inferType nenv usr cls rest*)
        return! failure "BLA"
        }
    | EMember (typ, name, exprs, rest) -> infer {
        // Extend the class env with the new implementor
        (*let cls =
            match lookup cls name with
            | Some set -> extend cls name (Set.add typ set)
            | None -> cls
        // Calculate the types we expect each member to be
        let etyps =
            exprs
            |> List.map (fun (name, ex) -> lookup env name |> Option.map snd)
            |> List.choose id
        // Calculate the actual types each member is inferred to
        let! atyps =
            exprs
            |> mapM (fun (name, ex) -> inferType env usr cls ex)
        let atyps = List.map snd atyps
        // If there is a mismatch in arity, throw an error
        if List.length etyps <> List.length atyps then
            return! failure <| sprintf "Error in typeclass instance."
        // Unify the actual and expected types gathering constraints. Don't apply these constraints
        let! subs = mapM (fun (e, a) -> unify e a) (List.zip etyps atyps)
        let subs = composeAll subs
        // If we have inferred 'this' to be something else than what we know it should
        // be, we have an error
        match lookup subs "this" |> Option.map (applyType subs), typ with
        | Some (TVar _), _ -> return! inferType env usr cls rest
        | Some ty, typ when typ <> ty -> return! failure "Invalid typeclass implementation."
        | _ -> return! inferType env usr cls rest*)
        return! failure "BLO"
        }
    | ERec e -> infer {
        let! _, (p1, t1) = inferType env usr cls e
        let! tv = fresh
        let! s2 = unify (TArrow (tv, tv)) t1
        return s2, (p1, applyType s2 tv)
        }

// Helpers to run
let inferProgramRepl typeEnv count e =
    inferType typeEnv Map.empty Map.empty e count // TODO: Include all the envs from REPL
    |> fun (ty, i) ->
        match ty with
        | Ok (subst, ty) -> Ok (renameFresh (applyScheme subst ty)), i
        | Error a -> Error (sprintf "%s" a), i

let inferProgram =
    inferProgramRepl (funSchemes) 0 >> fst