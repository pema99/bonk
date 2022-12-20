// Semantic checking which isn't type inference

module Semantics

open Repr
open Pretty

let rec cartesian lstlst =
    match lstlst with
    | h::[] ->
        List.fold (fun acc elem -> [elem]::acc) [] h
    | h::t ->
        List.fold (fun cacc celem ->
            (List.fold (fun acc elem -> (elem::celem)::acc) [] h) @ cacc
            ) [] (cartesian t)
    | _ -> []

(*
type AbstractPattern =
    | APName     of string
    | APGen      of string
    | APTuple    of AbstractPattern list
    | APUnion    of string * AbstractPattern
    | APConstant of Literal
    | APSeen     of Type * Literal Set

let rec abstractOverPattern pat =
    match pat with
    | PName name -> APName name
    | PTuple pats -> APTuple (List.map abstractOverPattern pats)
    | PUnion (name, pat) -> APUnion (name, abstractOverPattern pat)
    | PConstant lit -> APConstant lit

let rec renameInType (map: Map<string, Type>) (ty: Type) : Type =
    match ty with
    | TVar name -> Map.tryFind name map |> Option.defaultValue ty
    | TCtor (a, tys) -> TCtor (a, List.map (renameInType map) tys)
    | TArrow (a, b) -> TArrow (renameInType map a, renameInType map b)
    | _ -> ty

let concretizeType (env: UserEnv) (ty: Type) : Type =
    match ty with
    | TCtor (KSum name, tys) -> // tys = concrete types
        match Map.tryFind name env with
        | Some (tvars, cases) -> // tvars = generic types
            let map = Map.ofList (List.zip tvars tys)
            renameInType map ty
        | _ -> ty
    | _ -> ty

let rec getPossiblePatterns (env: UserEnv) (ty: Type) : AbstractPattern list =
    printfn "%A" ty
    match ty with
    | TConst "int" -> [APSeen (tInt, Set.empty)]
    | TConst "bool" -> [APConstant (LBool true); APConstant (LBool false)]
    | TConst "float" -> [APSeen (tFloat, Set.empty)]
    | TConst "string" -> [APSeen (tString, Set.empty)]
    | TConst "char" -> [APSeen (tChar, Set.empty)]
    | TConst "unit" -> [APConstant (LUnit)]
    | TVar a -> [APGen a]
    | TCtor (KProduct, tys) ->
        tys
        |> List.map (getPossiblePatterns env)
        |> cartesian
        |> List.map APTuple
    | TCtor (KSum name, tys) ->
        match Map.tryFind name env with
        | Some (tvars, variants) ->
            let map = Map.ofList (List.zip tvars tys)
            variants
            |> List.collect (fun (variant, ty2) ->
                getPossiblePatterns env (renameInType map ty2)
                |> List.map (fun pat -> APUnion (variant, pat)))
        | _ -> []
    | _ -> []

let rec isMatchedL (kind: AbstractPattern) (other: AbstractPattern) : bool =
    match kind, other with
    | APName _, _ -> true
    | APConstant l, APConstant r -> l = r
    | APTuple n, APTuple ps ->
        List.forall2 isMatchedL n ps
    | APUnion (ln, l), APUnion (rn, r) ->
        ln = rn && isMatchedL l r
    | _ -> false

let isMatched kind other =
    isMatchedL kind other || isMatchedL other kind

let rec addKnownPatternInfo a b =
    match a, b with
    | APSeen (sl, l), APSeen (_, r) -> APSeen (sl, Set.union l r)
    | APSeen (sl, l), APConstant r -> APSeen (sl, Set.add r l)
    | APConstant l, APSeen (sr, r) -> APSeen (sr, Set.add l r)
    | APTuple l, APTuple r -> APTuple (List.map2 addKnownPatternInfo l r)
    | APUnion (ln, l), APUnion (_, r) -> APUnion (ln, addKnownPatternInfo l r)
    | _ -> a

let findInvalidLiteral ty lits =
    match ty with
    | TConst "int" ->
        let ints = Seq.choose (function LInt i -> Some i | _ -> None) lits
        if Seq.isEmpty ints then LInt 0
        else LInt (Seq.max ints + 1)
    | TConst "float" ->
        let floats = Seq.choose (function LFloat f -> Some f | _ -> None) lits
        if Seq.isEmpty floats then LFloat 0
        else LFloat (Seq.max floats + 1.0)
    | TConst "string" ->
        let strings = Seq.choose (function LString s -> Some s | _ -> None) lits
        if Seq.isEmpty strings then LString "foo"
        else LString (Seq.maxBy (fun (s: string) -> s.Length) strings + "a")
    | TConst "char" ->
        let chars = Seq.choose (function LChar c -> Some c | _ -> None) lits
        if Seq.isEmpty chars then LChar 'a'
        else LChar (Seq.max chars + (char 1))
    | _ -> LUnit

let rec collapseKnownPatternInfo a =
    match a with
    | APSeen (ty, l) -> APConstant (findInvalidLiteral ty l)
    | APTuple l -> APTuple (List.map collapseKnownPatternInfo l)
    | APUnion (ln, l) -> APUnion (ln, collapseKnownPatternInfo l)
    | _ -> a

let findMissingMatch (env: UserEnv) (ty: Type)  (pats: Pattern list) : AbstractPattern option =
    let pats = List.map abstractOverPattern pats
    getPossiblePatterns env ty
    |> fun a -> printfn "%A - %A" ty a ; a
    |> List.tryFind (fun ctor -> not <| List.exists (isMatched ctor) pats)
    |> Option.map (fun ctor -> List.reduce addKnownPatternInfo (ctor :: pats))
    |> Option.map collapseKnownPatternInfo

let rec prettyAbstractPattern pat =
    match pat with
    | APName name -> name
    | APTuple pats -> sprintf "(%s)" (String.concat ", " (List.map prettyAbstractPattern pats))
    | APUnion (name, pat) -> sprintf "%s %s" name (prettyAbstractPattern pat)
    | APConstant lit -> prettyLiteral lit
    | APSeen (ty, lits) -> "?"
    | APGen name -> name

// TODO: Concretize type
// TODO: Deal with generic types

let getMatchError (env: UserEnv) (ty: Type) (pats: Pattern list) : string option =
    findMissingMatch env ty pats
    |> Option.map (fun pat -> sprintf "Pattern match is not exhaustive, for example, the value '%s' won't match." (prettyAbstractPattern pat))

let testFoo () =
    let fakeUEnv: UserEnv = Map.ofList [
        "Option", (["a"], [("Some", TVar "a"); ("None", tUnit)])
    ]
    let fakePats: Pattern list = [
        PUnion ("Some", PConstant (LInt 1))
        PUnion ("None", PName "_")
    ]
    let fakeType = TCtor (KSum "Option", [tInt])


    getMatchError fakeUEnv fakeType fakePats
    |> printfn "%A"

*)

type PatternCtor =
    | PCTuple                 // Tuples. K-ary ctor.
    | PCVariant of string     // Variant with given idx. K-ary ctor.
    | PCNonExhaustive         // Things that can't be matched exhaustively. Nullary ctor.
    | PCWildcard              // Wildcard (name) patterns. Nullary ctor.
    | PCMissing               // Missing pattern
    | PCRange of Literal list // Range of things we know // TODO:!!
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
    | (PConstant (LUnit), ty) -> // TODO: Is this right?
        { ctor = PCTuple; fields = []; ty = ty }
    | (PConstant c, ty) ->
        { ctor = PCOpaque; fields = []; ty = ty }
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

let rec isCoveredBy (self: PatternCtor) (other: PatternCtor) : bool =
    match self, other with
    | (_, PCWildcard) -> true
    | (PCMissing, _) -> false
    | (PCWildcard, _) -> false
    | (PCTuple, PCTuple) -> true
    | (PCVariant a, PCVariant b) -> a = b
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

let rec splitConstructor (ctx: PatternCtx) (self: PatternCtor) (ctors: PatternCtor list) : PatternCtor list =
    match self with
    | PCWildcard ->
        let allCtors =
            match ctx.colTy with
            | TConst "bool" -> [PCNonExhaustive] // TODO: PCRange!!!!
            | TConst "int" -> [PCNonExhaustive]
            | TConst "float" -> [PCNonExhaustive]
            | TConst "string" -> [PCNonExhaustive]
            | TConst "char" -> [PCNonExhaustive]
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
        if List.isEmpty missingCtors then
            allCtors
        else
            if List.isEmpty matrixCtors then
                [PCWildcard]
            else
                [PCMissing]
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

let applyConstructorMatrix (colTy: Type) (usefulness: Witness list) (mat: PatternMatrix) (ctor: PatternCtor) : Witness list =
    match usefulness with
    | [] -> []
    | _ ->
        match ctor with
        | PCMissing -> [[{ ctor = PCWildcard; fields = []; ty = colTy }]] //TODO: Make use of missing
        | _ -> usefulness |> List.map (fun witness -> applyConstructor colTy witness ctor)

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
                applyConstructorMatrix (ctx.colTy) usefulness rows ctor)
        ret

let testFoo () =
    let fakeUEnv: UserEnv = Map.ofList [
        "Option", (["a"], [("Some", TVar "a"); ("None", tUnit)])
    ]
    let fakeType = TCtor (KSum "Option", [tInt])
    let fakePats: PatternMatrix = [
        [deconstructPattern fakeUEnv fakeType (PUnion ("Some", PConstant (LBool true)))]
        [deconstructPattern fakeUEnv fakeType (PUnion ("Some", PConstant (LBool false)))]
        [deconstructPattern fakeUEnv fakeType (PUnion ("None", PName "_"))]

        //[deconstructPattern fakeType (PUnion ("None", PConstant (LUnit)))]
        //[deconstructPattern fakeType (PName "_")]
    ]
    let fakeNewPat: PatternStack = [deconstructPattern fakeUEnv fakeType (PUnion ("Some", PName "_"))]
    let usefulness = isUseful fakeUEnv fakePats fakeNewPat
    printfn "Useful: %A" (List.isEmpty usefulness |> not)
    ()