// Semantic checking which isn't type inference

module Semantics

open Repr
open Pretty

type PatternCtor =
    | PCTuple                 // Tuples. K-ary ctor.
    | PCVariant of string     // Variant with given idx. K-ary ctor.
    | PCNonExhaustive         // Things that can't be matched exhaustively. Nullary ctor.
    | PCWildcard              // Wildcard (name) patterns. Nullary ctor.
    | PCMissing               // Missing pattern
    | PCIntRange of int * int // Int range low-high (or bools), both inclusive.
    | PCOpaque                // Opaque type with nothing known

type DeconstructedPattern = {
    ctor: PatternCtor
    fields: DeconstructedPattern list
    ty: Type
}

type PatternCtx = {
    colTy: Type
    env: UserEnv
}

type PatternStack = DeconstructedPattern list
type PatternMatrix = PatternStack list
type PatternFields = DeconstructedPattern list
type Witness = DeconstructedPattern list

let rec deconstructPattern (env: UserEnv) (ty: Type) (pat: Pattern) : DeconstructedPattern =
    match (pat, ty) with
    | (PName _, ty) ->
        { ctor = PCWildcard; fields = []; ty = ty }
    | (PTuple ps, TCtor (KProduct, tys)) ->
        { ctor = PCTuple; fields = List.map2 (deconstructPattern env) tys ps; ty = ty }
    | (PUnion (name, pat), TCtor (KSum _, tys)) ->
        { ctor = PCVariant name; fields = List.map (fun nty -> deconstructPattern env nty pat) tys; ty = ty } // TODO: Is this right?!!!!!!!!!
    | (PConstant c, ty) ->
        let ctor = 
            match c with
            | LBool v   -> PCIntRange (if v then (1,1) else (0,0))
            | LChar v   -> PCIntRange (int v, int v)
            | LInt v    -> PCIntRange (v, v)
            | LUnit     -> PCTuple
            | LFloat v  -> PCOpaque
            | LString _ -> PCOpaque
        { ctor = ctor; fields = []; ty = ty }
    | _ ->
        failwith "Invalid call to deconstructPattern"

let wildcardsFromTypes (tys: Type list) : PatternFields =
    List.map (fun ty -> { ctor = PCWildcard; fields = []; ty = ty}) tys

let wildcards (colTy: Type) (ctor: PatternCtor) : PatternFields =
    match (ctor, colTy) with
    | (PCTuple, TCtor (KProduct, tys)) -> wildcardsFromTypes tys
    | (PCVariant _, TCtor (KSum _, tys)) -> wildcardsFromTypes tys // TODO: Is this right?!!!!!!!!
    | _ -> []

// S(c, pat)
let rec specialize (colTy: Type) (ctor: PatternCtor) (pat: DeconstructedPattern) : PatternStack =
    match (pat.ctor, ctor) with
    | (PCWildcard, _) -> wildcards colTy ctor 
    | _ -> pat.fields

// Does 'self' match a subset of what 'other' does?
let rec isCoveredBy (self: PatternCtor) (other: PatternCtor) : bool =
    match self, other with
    | (_, PCWildcard) -> true
    | (PCMissing, _) -> false
    | (PCWildcard, _) -> false
    | (PCTuple, PCTuple) -> true
    | (PCVariant a, PCVariant b) -> a = b
    | (PCIntRange (lf,lt), PCIntRange (rf,rt)) -> lf >= rf && lt <= rt
    | (PCOpaque, _) -> false
    | (_, PCOpaque) -> false
    | (PCNonExhaustive, _) -> false
    | _ -> failwith "Incompatible constructors"

let rec popHeadConstructor (colTy: Type) (pat: PatternStack) (ctor: PatternCtor) : PatternStack =
    let newFields = pat |> List.head |> specialize colTy ctor
    newFields @ List.tail pat

let rec specializeMatrix (colTy: Type) (ctor: PatternCtor) (mat: PatternMatrix) : PatternMatrix =
    mat
    |> List.filter (fun row -> isCoveredBy ctor (List.head row).ctor)
    |> List.map (fun row -> popHeadConstructor colTy row ctor)

let rec splitWildcard (ctx: PatternCtx) (ctors: PatternCtor list) : (PatternCtor list * PatternCtor list * PatternCtor list) =
    let allCtors =
        match ctx.colTy with
        | TConst "bool" -> [PCIntRange (0, 1)]
        | TConst "int" -> [PCIntRange (System.Int32.MinValue, System.Int32.MaxValue)]
        | TConst "float" -> [PCNonExhaustive]
        | TConst "string" -> [PCNonExhaustive]
        | TConst "char" -> [PCIntRange (int System.Char.MinValue, int System.Char.MaxValue)]
        | TConst "unit" -> [PCTuple]
        | TCtor (KProduct, _) -> [PCTuple]
        | TCtor (KSum name, tys) ->
            match Map.tryFind name ctx.env with
            | Some (_, variants) -> List.map (fst >> PCVariant) variants
            | None -> failwith "Invalid variant" // TODO: Handle error
        | _ -> [PCNonExhaustive]
    let allCtors =
        allCtors |> List.collect (fun ctor -> splitConstructor ctx ctor ctors)
    let matrixCtors =
        ctors |> List.filter (function PCWildcard -> false | _ -> true)
    let missingCtors =
        allCtors |> List.filter (fun ctor -> not <| List.exists (isCoveredBy ctor) matrixCtors)
    (matrixCtors, allCtors, missingCtors)

and splitConstructor (ctx: PatternCtx) (self: PatternCtor) (ctors: PatternCtor list) : PatternCtor list =
    match self with
    | PCWildcard ->
        let (matrixCtors, allCtors, missingCtors) = splitWildcard ctx ctors
        if List.isEmpty missingCtors then
            allCtors
        else
            if List.isEmpty matrixCtors then
                [PCWildcard]
            else
                [PCMissing]
    | PCIntRange (f, t) ->
        let subtractRanges (lf, lt) (rf, rt) =
            if rf <= lf && rt >= lt then []               // completely contained
            else if lf > rt then [(lf, lt)]               // no overlap
            else if lt < rf then [(lf, lt)]               // no overlap
            else if rt < lt && rf <= lf then [(rt+1, lt)] // cut off left side
            else if rt >= lt && rf > lf then [(lf, rf-1)] // cut off right side
            else [(lf, rf-1); (rt+1, lt)]                 // split into 2 intervals
        ctors
            |> List.choose (function PCIntRange (a, b) -> Some (a, b) | _ -> None) // extract ranges
            |> List.fold (fun fs (a, b) ->                                         // remove ranges 1 by 1
                List.collect (fun me -> subtractRanges me (a, b)) fs
                ) [(f, t)]
            |> List.map PCIntRange
    | _ -> [self]

let applyConstructor (colTy: Type) (witness: Witness) (ctor: PatternCtor) : Witness =
    let arity =
        match (ctor, colTy) with
        | (PCTuple, TCtor (KProduct, tys)) -> List.length tys
        | (PCVariant _, _) -> 1
        | _ -> 0
    let newPat = {
        ctor = ctor
        fields = List.take arity witness// TODO: Is this right? Should be reversed?
        ty = colTy
    }
    newPat :: List.skip arity witness

let applyConstructorMatrix (ctx: PatternCtx) (witnesses: Witness list) (mat: PatternMatrix) (ctor: PatternCtor) : Witness list =
    match witnesses with
    | [] -> []
    | _ ->
        match ctor with
        | PCMissing ->
            let (_, _, missingCtors) = splitWildcard ctx (List.map (fun row -> (List.head row).ctor) mat)
            let newPats =
                missingCtors
                |> List.map (fun missing ->
                    let wilds = wildcards ctx.colTy missing
                    { ctor = missing; fields = wilds; ty = ctx.colTy })
            witnesses
            |> List.collect (fun witness ->
                newPats |> List.map (fun pat ->
                    witness @ [pat]))
        | _ -> witnesses |> List.map (fun witness -> applyConstructor ctx.colTy witness ctor)

// Is pattern v useful w.r.t known patterns in rows. If so, return witnesses to usefulness.
let rec isUseful (env: UserEnv) (rows: PatternMatrix) (v: PatternStack) : Witness list =
    match v with
    | [] when List.isEmpty rows -> [[]] // Useful, with trivial witness
    | [] -> []                          // Not useful
    | h::t ->                           // Recursive case
        let colTy = h.ty
        let vCtor = h.ctor
        let ctx = { colTy = colTy; env = env }
        let splitCtors = splitConstructor ctx vCtor (List.map (fun row -> (List.head row).ctor) rows)
        let ret =
            splitCtors |> List.collect (fun ctor ->
                let specMatrix = specializeMatrix (ctx.colTy) ctor rows
                let v = popHeadConstructor (ctx.colTy) v ctor
                let usefulness = isUseful ctx.env specMatrix v
                applyConstructorMatrix ctx usefulness rows ctor)
        ret

let testFoo () =
    let fakeUEnv: UserEnv = Map.ofList [
        "Option", (["a"], [("Some", TVar "a"); ("None", tUnit)])
    ]
    let fakeType = TCtor (KSum "Option", [tBool])
    let fakePats: PatternMatrix = [
        //[deconstructPattern fakeUEnv fakeType (PUnion ("Some", PConstant (LBool true)))]
        [deconstructPattern fakeUEnv fakeType (PUnion ("Some", PConstant (LBool false)))]
        [deconstructPattern fakeUEnv fakeType (PUnion ("None", PName "_"))]
        //[deconstructPattern fakeUEnv fakeType (PConstant (LBool false))]

        //[deconstructPattern fakeType (PUnion ("None", PConstant (LUnit)))]
        //[deconstructPattern fakeType (PName "_")]
    ]
    let fakeNewPat: PatternStack = [deconstructPattern fakeUEnv fakeType (PName "_")]
    let usefulness = isUseful fakeUEnv fakePats fakeNewPat
    printfn "Useful: %A" (List.isEmpty usefulness |> not)
    printfn "%A\n" usefulness
    ()