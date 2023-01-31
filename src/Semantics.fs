// Semantic checking which isn't type inference

module Semantics

open Repr
open ReprUtil
open Prelude
open Pretty
open Monad

// The code below performs exhaustiveness checking for pattern matching.
// It is quite heavily based on the Rust compilers implementation:
// - https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
// Which in turn is based on this paper from Inria:
// - http://moscova.inria.fr/~maranget/papers/warn/index.html
//
// The basic idea is, given a set of patterns P, and a new pattern Q, to compute a 'usefulnes' metric for Q.
// Concretely, this is a possibly empty set of values (represented as patterns that match them),
// which are matched by Q, but not by any of the patterns in P. Once we have the ability to calculate this,
// we can determine whether the patterns in P are exhaustive, by calculating the usefulness of the wildcard
// pattern. If a wildcard can match _anything_ which P cannot, then P is not exhaustive. A similar idea can
// be used to calculate reachability.

// Different kinds of patterns, not all corresponding to patterns in the source language.
type PatternCtor =
    | PCTuple                 // Tuples. K-ary ctor.
    | PCVariant of string     // Variant with given idx. K-ary ctor.
    | PCNonExhaustive         // Things that can't be matched exhaustively. Nullary ctor.
    | PCWildcard              // Wildcard (name) patterns. Nullary ctor.
    | PCMissing               // Missing pattern
    | PCIntRange of int * int // Int range low-high (or bools), both inclusive.
    | PCOpaque                // Opaque type with nothing known

// Flat representation of a pattern, easy to manipulate.
type DeconstructedPattern = {
    ctor: PatternCtor
    fields: DeconstructedPattern list
    ty: Type
}

// Stuff we need while running the algorithm.
type PatternCtx = {
    colTy: Type  // Type of values matched by pattern in the current leftmost matrix column.
    env: UserEnv // Used for looking up user-defined types.
}

type PatternStack = DeconstructedPattern list  // Matrix row.
type PatternMatrix = PatternStack list         // Full matrix.
type PatternFields = DeconstructedPattern list // Fields contained in a deconstructed pattern.
type Witness = DeconstructedPattern list       // Witness of usefulness, equivalent to a row.

// Convert a pattern to a deconstructed pattern.
let rec deconstructPattern (env: UserEnv) (ty: Type) (pat: Pattern) : DeconstructedPattern =
    match (pat, ty) with
    | (PName _, ty) ->
        { ctor = PCWildcard; fields = []; ty = ty }
    | (PTuple ps, TCtor (KProduct, tys)) ->
        { ctor = PCTuple; fields = List.map2 (deconstructPattern env) tys ps; ty = ty }
    | (PUnion (variant, pat), TCtor (KSum klass, tys)) ->
        // To find the fields, we need to instantiate the specific variant
        // since it might be generic.
        let instCaseTy = instantiateVariant env klass variant tys
        let fields =
            match instCaseTy, pat with
            | Some v, Some pat -> [deconstructPattern env v pat]
            | None, None -> []
            | _ -> failwith "Invalid call to deconstructPattern"
        { ctor = PCVariant variant; fields = fields; ty = ty }
    | (PConstant c, ty) ->
        let ctor = 
            match c with
            | LBool v   -> PCIntRange (if v then (1,1) else (0,0))
            | LChar v   -> PCIntRange (int v, int v)
            | LInt v    -> PCIntRange (v, v)
            | LUnit     -> PCTuple
            | LFloat _  -> PCOpaque
            | LString _ -> PCOpaque
        { ctor = ctor; fields = []; ty = ty }
    | _ ->
        failwith "Invalid call to deconstructPattern"

// Used for creating fake versions of a pattern with all fields replace by wildcards.
let wildcardsFromTypes (tys: Type list) : PatternFields =
    List.map (fun ty -> { ctor = PCWildcard; fields = []; ty = ty}) tys

let wildcards (ctx: PatternCtx) (ctor: PatternCtor) : PatternFields =
    match (ctor, ctx.colTy) with
    | (PCTuple, TCtor (KProduct, tys)) -> wildcardsFromTypes tys
    | (PCVariant variant, TCtor (KSum klass, tys)) ->
        let instCaseTy = instantiateVariant ctx.env klass variant tys
        match instCaseTy with
        | Some v -> wildcardsFromTypes [v]
        | None -> []
    | _ -> []

// Specialize 'pat' with 'ctor', yielding either nothing if the constructor doesn't match,
// or the fields contained within 'pat' if it does.
let rec specialize (ctx: PatternCtx) (ctor: PatternCtor) (pat: DeconstructedPattern) : PatternStack =
    match (pat.ctor, ctor) with
    | (PCWildcard, _) -> wildcards ctx ctor 
    | _ -> pat.fields

// Does 'self' match a subset of the values that 'other' matches?
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

// Specialization for an entire matrix.
let rec popHeadConstructor (ctx: PatternCtx) (pat: PatternStack) (ctor: PatternCtor) : PatternStack =
    let newFields = pat |> List.head |> specialize ctx ctor
    newFields @ List.tail pat

let rec specializeMatrix (ctx: PatternCtx) (ctor: PatternCtor) (mat: PatternMatrix) : PatternMatrix =
    mat
    |> List.filter (fun row -> isCoveredBy ctor (List.head row).ctor)
    |> List.map (fun row -> popHeadConstructor ctx row ctor)

// Split the wildcard pattern for a type into all possible pattern constructors for the type,
// modulo those already matched by patterns in the matrix, ie. 'ctors'.
let rec splitWildcard (ctx: PatternCtx) (ctors: PatternCtor list) : (PatternCtor list * PatternCtor list * PatternCtor list) =
    let allCtors =
        match ctx.colTy with
        | TConst TBool -> [PCIntRange (0, 1)]
        | TConst TInt -> [PCIntRange (System.Int32.MinValue, System.Int32.MaxValue)]
        | TConst TFloat -> [PCNonExhaustive]
        | TConst TString -> [PCNonExhaustive]
        | TConst TChar -> [PCIntRange (int System.Char.MinValue, int System.Char.MaxValue)]
        | TConst TUnit -> [PCTuple]
        | TCtor (KProduct, _) -> [PCTuple]
        | TCtor (KSum name, _) ->
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

// Split a pattern constructor into all possible concrete pattern constructors corresponding to it,
// modulo those already matched by patterns in the matrix, ie. 'ctors'. This basically tells us what
// which possible patterns we have left to check during our run of the algorithm.
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

// Apply a constructor to a witness. Inverse of specialization.
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

// Same as above but for entire matrix.
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
                    let wilds = wildcards ctx missing
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
    | h::_ ->                           // Recursive case
        let colTy = h.ty
        let vCtor = h.ctor
        let ctx = { colTy = colTy; env = env }
        let splitCtors = splitConstructor ctx vCtor (List.map (fun row -> (List.head row).ctor) rows)
        let ret =
            splitCtors |> List.collect (fun ctor ->
                let specMatrix = specializeMatrix ctx ctor rows
                let v = popHeadConstructor ctx v ctor
                let usefulness = isUseful ctx.env specMatrix v
                applyConstructorMatrix ctx usefulness rows ctor)
        ret

// Essentially identity monad used for stateless error checking
type CheckM<'t> = ResultM<'t,ErrorInfo>
let check = state
let runCheckM m =
    m () |> fst

let checkMatch (env: UserEnv) (sp: Span) (matcher: Type) (pats: Pattern list) : CheckM<unit> = check {
    let patMatrix = List.map (deconstructPattern env matcher >> List.singleton) pats
    let wildcardPat = [deconstructPattern env matcher (PName "_")]
    let witnesses = isUseful env patMatrix wildcardPat
    if not <| List.isEmpty witnesses then
        do! failure { span = sp; msg = "Match is not exhaustive." }
    }

let checkMatches (env: UserEnv) (decls: TypedDecl list) : CheckM<TypedDecl list> =
    traverseTypedDecls 
        (fun ex -> check {
            match ex.kind with
            | EMatch (e1, bs) ->
                do! checkMatch env (ex.span) (snd e1.data) (List.map fst bs)
                return ex
            | ELet (p, e1, _) ->
                do! checkMatch env (ex.span) (snd e1.data) [p]
                return ex
            | ELam (p, _) ->
                match snd ex.data with
                | TCtor (KArrow, [inp; _]) ->
                    do! checkMatch env (ex.span) inp [p]
                    return ex
                | _ -> return ex
            | _ -> return ex
        })
        (fun decl -> check {
            match decl.kind with
            | DLet (p, e) ->
                do! checkMatch env (decl.span) (snd e.data) [p]
                return decl
            | _ -> return decl
        })
        decls

// Function coloring analysis
// Fun impures, exceptions, class impures
type ColorM<'t> = StateM<(string Set * string Set * string Set),'t,ErrorInfo>
let color = state
let runColorM m =
    m (funImpures, funImpureExceptions, Set.empty) |> fst

// Helpers to set state
let getImpures = get
let setImpures impures = fun _ -> (Ok (), (impures))

// Remove bindings which are about to be shadowed, and are pure.
let removeBound (pat: Pattern) (impures: string Set) : string Set =
    (Set.difference impures (freeInPattern pat)) 

// Is the expression pure given the set of impure bindings?
let rec isExprPure (impures: string Set) (ex: TypedExpr) : bool =
    match ex.kind with
    | ELit _ ->
        true
    | EVar name -> // Pure if not in impure set
        not <| Set.contains name impures
    | EApp (f, x) -> 
        isExprPure impures f && isExprPure impures x
    | ELam (pat, e) -> // Remove bound lambda inputs from impures, they are shadowed
        isExprPure (removeBound pat impures) e
    | ELet (pat, e1, e2) -> // Remove binding from impures, but ONLY in the second expression
        isExprPure impures e1 && isExprPure (removeBound pat impures) e2
    | EIf (cond, tr, fl) ->
        isExprPure impures cond && isExprPure impures tr && isExprPure impures fl
    | EOp (l, _, r) ->
        isExprPure impures l && isExprPure impures r
    | ETuple (es) ->
        List.forall (isExprPure impures) es
    | EMatch (_, bs) -> // Remove relevant binding from impures for each match arm
        List.forall (fun (pat, ex) -> isExprPure (removeBound pat impures) ex) bs
    | EGroup (bs, rest) -> // Remove relevant bindings from impures for each group and rest - these are recursive
        let impures = Set.difference impures (List.map fst bs |> Set.ofList)
        List.forall (snd >> isExprPure impures) bs && isExprPure impures rest
    | ERaw _ ->
        false

// Is the type inherently pure - IE, plain old data?
let rec isInherentlyPureType (ty: Type) : bool =
    match ty with
    | TVar _ -> false         // Can't know
    | TCtor (KArrow, _) -> false // Might contain impure call
    | TConst TOpaque -> false // Can't know
    | TConst _ -> true
    | TCtor (KProduct, tys)
    | TCtor (KSum _, tys) ->
        List.forall isInherentlyPureType tys
    | _ -> false

let checkPurity (decls: TypedDecl list) : ColorM<TypedDecl list> =
    traverseTypedDecls
        (just)
        (fun decl -> check {
            let hasImpureQual = Set.contains QImpure decl.qualifiers
            let hasMemoizeQual = Set.contains QMemoize decl.qualifiers 
            let! sets = getImpures
            let (impures, excepts, classImpures) = sets
            match decl.kind with
            | _ when hasImpureQual && hasMemoizeQual ->
                return! failure { span = decl.span; msg = "Impure functions cannot be memoized." }
            | (DLet (PTuple _, _) | DLet (PUnion _, _) | DLet (PConstant _, _)) when hasMemoizeQual ->
                return! failure { span = decl.span; msg = "Memoized functions cannot be defined with a pattern match." }
            | (DClass _ | DMember _) when hasMemoizeQual ->
                return! failure { span = decl.span; msg = "Memoize is an invalid qualifier for this syntax element." }
            | DLet (PName name, _)
            | DGroup ([name, _]) when Set.contains name excepts ->
                // TODO: Handle the case where the user defines a function with the
                // same name as an exception.
                return decl
            | DLet (p, e) ->
                let isBodyImpure = not <| isExprPure impures e
                let isInherentlyPure = isInherentlyPureType (snd e.data)
                let isImpure = (not isInherentlyPure) && (hasImpureQual || isBodyImpure)
                if isImpure then
                    let impures = Set.union impures (freeInPattern p)
                    do! setImpures (impures, excepts, classImpures)
                if isImpure && not hasImpureQual then
                    return! failure { span = decl.span; msg = "Impure binding must be marked with an impure qualifier." }
                else
                    return decl
            | DGroup bs ->
                let fakeExpr = mkFakeExpr (EGroup (bs, mkFakeExpr (ELit LUnit)))
                let isBodyImpure = not <| isExprPure impures fakeExpr
                let isInherentlyPure = List.forall (fun (_, e: TypedExpr) -> isInherentlyPureType (snd e.data)) bs
                let isImpure = (not isInherentlyPure) && (hasImpureQual || isBodyImpure)
                if isImpure then
                    let impures = Set.union impures (List.map fst bs |> Set.ofList)
                    do! setImpures (impures, excepts, classImpures)
                if isImpure && not hasImpureQual then
                    return! failure { span = decl.span; msg =  "Impure binding must be marked with an impure qualifier." }
                else
                    return decl
            | DClass (name, _, _) when hasImpureQual ->
                // TODO: Make this more granular
                let classImpures = Set.add name classImpures
                do! setImpures (impures, excepts, classImpures)
                return decl
            | DMember ((name, _), impls) ->
                let isClassImpure = Set.contains name classImpures
                let isBodyImpures = List.map (fun (impl, ex) ->
                    let isBodyImpure = not <| isExprPure impures ex
                    let isInherentlyPure = isInherentlyPureType (snd ex.data)
                    impl, (not isInherentlyPure) && (hasImpureQual || isBodyImpure)) impls
                if List.exists snd isBodyImpures && not isClassImpure then
                    return! failure { span = decl.span; msg = "Impure bindings are not allowed in typeclasses unless the typeclass has the impure qualifier." }
                else
                    let implImpures = List.filter snd isBodyImpures |> List.map fst
                    let impures = Set.union impures (Set.ofList implImpures)
                    do! setImpures (impures, excepts, classImpures)
                    return decl
            | _ ->
                if Set.isEmpty decl.qualifiers then
                    return decl
                else
                    return! failure { span = decl.span; msg = "Qualifiers are invalid for this type of syntax element." }
        })
        decls

// Put it all together
let checkPrograms (env: UserEnv, decls: TypedProgram list) : Result<TypedProgram list, FileErrorInfo> =
    decls
    |> (mapM (withFileErrorInfoM (checkMatches env)) >> runCheckM)
    |> Result.bind (mapM (withFileErrorInfoM (checkPurity)) >> runColorM)