module Pretty

open Repr

let printColor str =
    let rec cont str =
        match str with
        | h :: (t :: r) when h = '$' ->
                match t with
                | 'r' -> System.Console.ForegroundColor <- System.ConsoleColor.Red
                | 'g' -> System.Console.ForegroundColor <- System.ConsoleColor.Green
                | 'b' -> System.Console.ForegroundColor <- System.ConsoleColor.Blue
                | 'y' -> System.Console.ForegroundColor <- System.ConsoleColor.Yellow
                | _ -> System.Console.ForegroundColor <- System.ConsoleColor.White
                cont r
        | h :: t ->
                printf "%c" h
                cont t
        | _ -> ()
    cont (Seq.toList str)
    printfn ""
    System.Console.ForegroundColor <- System.ConsoleColor.White

let prettyTypeName (i: int) : string =
    if i < 26 then string <| 'a' + char i
    else sprintf "t%A" i

let rec renameFreshInner (t: Type) subst count =
    match t with
    | TConst _ -> t, subst, count
    | TVar a ->
        match Map.tryFind a subst with
        | Some v -> TVar v, subst, count
        | None ->
            let name = prettyTypeName count
            let nt = TVar name
            nt, Map.add a name subst, count + 1
    | TCtor (kind, args) ->
        let lst =
            args
            |> List.scan (fun (_, subst, count) x -> renameFreshInner x subst count) (tVoid, subst, count)
            |> List.tail
        let args, substs, counts = List.unzip3 lst
        TCtor (kind, args),
        List.tryLast substs |> Option.defaultValue subst,
        List.tryLast counts |> Option.defaultValue count

let renameFreshType t =
    let (t, _, _) = renameFreshInner t Map.empty 0
    t

let renameFreshQualType (t: QualType) =
    let a, b = t
    let b, s, c = renameFreshInner b Map.empty 0
    let a = Seq.scan (fun (_, (_, s, c)) (ps, v) -> ps, renameFreshInner v s c) ("", (tVoid, s, c)) a
    let a = Seq.map (fun (a, (b, _, _)) -> a, b) (Seq.tail a)
    (Set.ofSeq a, b)

let rec prettyTypeInner (t: Type) : string =
    match t with
    | TConst v ->
        match v with
        | TInt -> "int"
        | TBool -> "bool"
        | TFloat -> "float"
        | TString -> "string"
        | TChar -> "char"
        | TVoid -> "void"
        | TUnit -> "unit"
        | TOpaque -> "opaque"
    | TVar v -> sprintf "'%s" v
    | TCtor (kind, args) ->
        match kind with
        | KProduct _ ->
            args
            |> List.map prettyTypeInner
            |> List.toArray
            |> String.concat " * "
            |> sprintf "(%s)"
        | KSum name ->
            let fmt =
                args
                |> List.map prettyTypeInner
                |> List.toArray
                |> String.concat ", "
            if fmt = "" then name
            else sprintf "%s<%s>" name fmt
        | KArrow ->
            match args with
            | [l; r] -> sprintf "(%s -> %s)" (prettyTypeInner l) (prettyTypeInner r)
            | _ -> failwith "Invalid arrow type"

let prettyType =
    renameFreshType >> prettyTypeInner

let prettyQualTypeInner (t: QualType) =
    let a, b = t
    let preds =
        Set.map (fun (c, d) -> c, prettyTypeInner d) a
        |> Set.map (fun (c, d) -> sprintf "%s %s" c d)
        |> String.concat ", "
    if Set.count a > 0 then
        sprintf "(%s) => %s" preds (b |> prettyTypeInner)
    else
        (b |> prettyTypeInner)

let prettyQualType =
    renameFreshQualType >> prettyQualTypeInner

let rec prettyValue v =
    match v with
    | VUnit -> "()"
    | VInt v -> string v
    | VBool v -> string v
    | VFloat v -> string v
    | VString v -> sprintf "%A" v
    | VChar v -> sprintf "'%c'" v
    | VTuple v -> sprintf "(%s)" <| String.concat ", " (List.map prettyValue v)
    | VUnionCase (n, v) -> sprintf "%s %s" n (prettyValue v)
    | VClosure _ | VUnionCtor _ | VIntrinsic _ | VOverload _ -> "Closure"

let prettyLiteral = function
    | LInt v -> string v
    | LBool v -> string v
    | LFloat v -> string v
    | LString v -> sprintf "\"%s\"" v
    | LChar v -> sprintf "'%c'" v
    | LUnit -> "()"

// Errors
let prettyError ({file = filename; span = span; msg = msg }) : string =
    let (start, stop) = span
    let preamble = sprintf "Error: %s\n --> %s:%i:%i\n" msg filename (fst start) (snd start)
    if fst start <= 0 || snd start <= 0 then
        preamble
    else
        let lines = System.IO.File.ReadAllLines filename
        let line = lines.[fst start - 1]
        let fakeLineNum = String.replicate (string (fst start)).Length " " + " | "
        let lineNum = sprintf "%i | " (fst start)
        let mid = sprintf "%s\n%s%s\n%s" fakeLineNum lineNum line fakeLineNum
        if fst start = fst stop then
            let dist = snd stop - snd start
            let spaces = String.replicate (snd start - 1) " "
            let caret = String.replicate dist "^"
            preamble + mid + spaces + caret
        else
            preamble + mid