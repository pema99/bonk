module Pretty

open Repr

let rec prettyPattern pat =
    match pat with
    | PName a -> a
    | PTuple pats  -> String.concat ", " (List.map prettyPattern pats)
    | PUnion (case, pat) -> sprintf "%s %s" case (prettyPattern pat)
    | _ -> "?"

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

let rec prettyType (t: Type) : string =
    match t with
    | TConst v -> v
    | TVar v -> sprintf "'%s" v
    | TArrow (l, r) -> sprintf "(%s -> %s)" (prettyType l) (prettyType r) 
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

let prettyTypeName (i: int) : string =
    if i < 26 then string <| 'a' + char i
    else sprintf "t%A" i

let rec renameFreshInner (t: Type) subst count =
    match t with
    | TConst _ -> t, subst, count
    | TArrow (l, r) ->
        let (r1, subst1, count1) = renameFreshInner l subst count
        let (r2, subst2, count2) = renameFreshInner r subst1 count1
        TArrow (r1, r2), subst2, count2
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
    renameFreshInner t Map.empty 0

let prettyQualType (t: QualType) =
    let a, b = t
    let preds =
        List.map (fun (c, d) -> c, prettyType d) a
        |> List.map (fun (c, d) -> sprintf "%s %s" c d)
        |> String.concat ", "
    if List.length a > 0 then
        sprintf "(%s) => %s" preds (b |> prettyType)
    else
        (b |> prettyType)

let renameFreshQualType (t: QualType) =
    let a, b = t
    let b, s, c = renameFreshInner b Map.empty 0
    let a = List.scan (fun (_, (_, s, c)) (ps, v) -> ps, renameFreshInner v s c) ("", (tVoid, s, c)) a
    let a = List.map (fun (a, (b, _, _)) -> a, b) (List.tail a)
    (a, b)

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