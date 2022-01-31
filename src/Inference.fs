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
  member this.Fresh() : InferM<Type> =
    fun s -> Ok (TVar (sprintf "_t%A" s)), s + 1

let infer = InferenceBuilder()
let just = infer.Return
let fresh = infer.Fresh
let failure err = fun s -> Error err, s
let rec mapM (f: 'a -> InferM<'b>) (t: 'a list) : InferM<'b list> = infer {
    match t with
    | h :: t ->
        let! v = f h
        let! next = mapM f t
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

let applyType =
    let rec applyTypeFP (s: Substitution) (t: Type) : Type =
        match t with
        | TCon _ -> t
        | TVar a -> Map.tryFind a s |> Option.defaultValue t
        | TArr (t1, t2) -> TArr (applyTypeFP s t1 , applyTypeFP s t2)
    fixedPoint applyTypeFP

let ftvScheme (sc: Scheme) : string Set =
    let a, t = sc
    Set.difference (ftvType t) (Set.ofList a) 

let applyScheme =
    let rec applySchemeFP (s: Substitution) (sc: Scheme) : Scheme =
        let a, t = sc
        let s' = List.fold (fun acc k -> Map.remove k acc) s a // TODO: Is this right?
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
    | _ ->
        return! failure <| sprintf "Failed to unify types %A and %A" t1 t2
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

// Inference
let rec inferExpr (env: TypeEnv) (e: Expr) : InferM<Substitution * Type> =
    match e with
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
            return! failure <| sprintf "Inference failure, use of unbound variable %A" a
        }
    | App (f, x) -> infer {
        let! tv = fresh()
        let! s1, t1 = inferExpr env f
        let! s2, t2 = inferExpr (applyEnv s1 env) x
        let! s3 = unify (applyType s2 t1) (TArr (t2, tv))
        return (compose s3 (compose s2 s1), applyType s3 tv)
        }
    | Lam (x, e) -> infer {
        let! tv = fresh()
        let nenv = extend env x ([], tv)
        let! s1, t1 = inferExpr nenv e
        return (s1, TArr (applyType s1 tv, t1))
        }
    | Let (x, e1, e2) -> infer {
        let! s1, t1 = inferExpr env e1
        let nenv = applyEnv s1 env
        let nt = generalize nenv t1
        let! s2, t2 = inferExpr (extend env x nt) e2
        return (compose s1 s2, t2)
        }
    | If (cond, tr, fl) -> infer {
        let! s1, t1 = inferExpr env cond
        let env = applyEnv s1 env
        let! s2, t2 = inferExpr env tr
        let env = applyEnv s1 env
        let! s3, t3 = inferExpr env fl
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
        let! s1, t1 = inferExpr env l
        let! s2, t2 = inferExpr env r
        let! tv = fresh()
        let scheme = Map.find op ops
        let! inst = instantiate scheme
        let! s3 = unify (TArr (t1, TArr (t2, tv))) inst
        return (compose s1 (compose s2 s3), applyType s3 tv)
        }
    | Rec e -> infer {
        let! _, t1 = inferExpr env e
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
    let (res, _, _) = cont t Map.empty 0
    res

let rec prettyType (t: Type) : string =
    match t with
    | TCon v -> v
    | TVar v -> sprintf "'%s" v
    | TArr (l, r) -> sprintf "(%s -> %s)" (prettyType l) (prettyType r) 

let inferProgram e =
    inferExpr Map.empty e 0
    |> fst
    |> Result.map (snd >> renameFresh)