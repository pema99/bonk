module Pretty

open Repr
open Monad

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
        let (kind, subst, count) =
            match kind with
            | KVar name ->
                let tvar, subst, count = renameFreshInner (TVar name) subst count
                match tvar with
                | TVar v -> KVar v, subst, count
                | _ -> kind, subst, count
            | _ -> kind, subst, count
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
        | KVar name ->
            let fmt =
                args
                |> List.map prettyTypeInner
                |> List.toArray
                |> String.concat ", "
            if fmt = "" then name
            else sprintf "'%s<%s>" name fmt
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
    | VUnionCase (n, Some v) -> sprintf "%s %s" n (prettyValue v)
    | VUnionCase (n, None) -> n
    | VClosure _ | VUnionCtor _ | VIntrinsic _ | VOverload _ -> "Closure"

let prettyLiteral = function
    | LInt v -> string v
    | LBool v -> string v
    | LFloat v -> string v
    | LString v -> sprintf "'%s'" v
    | LChar v -> sprintf "'%c'" v
    | LUnit -> "()"

let rec prettyPattern = function
    | PName x -> x
    | PTuple xs -> List.map prettyPattern xs |> String.concat ", " |> sprintf "(%s)"
    | PUnion (n, Some p) -> n + " (" + prettyPattern p + ")"
    | PUnion (n, None) -> n
    | PConstant n -> prettyLiteral n

let rec prettyOp = function
    | Plus -> "+"
    | Minus -> "-"
    | Star -> "*"
    | Slash -> "/"
    | Equal -> "="
    | NotEq -> "!="
    | Greater -> ">"
    | GreaterEq -> ">="
    | Less -> "<"
    | LessEq -> "<="
    | BoolAnd -> "&&"
    | BoolOr -> "||"
    | Modulo -> "%"

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

// Mermaid
type MermaidM<'t> = StateM<int * string, 't, unit>
let bumpIdx: MermaidM<unit> = fun (i, s) -> Ok (), (i+1, s)
let getIdx: MermaidM<int> = fun (i, s) -> Ok i, (i, s)
let getNext: MermaidM<int> = fmap ((+)1) getIdx
let add (s: string): MermaidM<unit> = fun (i, s') -> Ok (), (i, s' + "\n" + s)

type MermaidBuilder() =
    inherit StateBuilder()
    member inline this.Yield(x: string): MermaidM<string> =
        fun (i, s) -> Ok x, (i, s + x + "\n")
    member inline this.YieldFrom(x: MermaidM<string>): MermaidM<string> =
        fun (i, s) -> x (i, s)
    member inline this.For (lst: seq<'T>, f: 'T -> MermaidM<string>): MermaidM<string> =
        fmap (String.concat "\n") <| mapM f (Seq.toList lst)

let mermaid = MermaidBuilder()

let inline linkNext (me: int) (m: MermaidM<string>): MermaidM<string> = mermaid {
    let! next = getNext
    yield sprintf "%i---%i" me next
    yield! m
}

let rec prettyMermaidExpr (ast: ExprRaw<'t>): MermaidM<string> = mermaid {
    do! bumpIdx
    let! me = getIdx
    match ast.kind with
    | EVar v ->
        yield sprintf "%i[\"%s\"]" me v
    | EApp (f, x) ->
        yield sprintf "%i[apply]" me
        let! s = get
        yield! linkNext me (prettyMermaidExpr f)
        yield! linkNext me (prettyMermaidExpr x)
    | ELam (v, b) ->
        yield sprintf "%i[\"\\%s\"]" me (prettyPattern v)
        yield! linkNext me (prettyMermaidExpr b)
    | ELet (v, e, b) ->
        yield sprintf "%i[\"let %s\"]" me (prettyPattern v)
        yield! linkNext me (prettyMermaidExpr e)
        yield! linkNext me (prettyMermaidExpr b)
    | ELit (LString "") ->
        yield sprintf "%i[\" \"]" me
    | ELit l ->
        yield sprintf "%i[\"%s\"]" me (prettyLiteral l)
    | EIf (c, t, f) ->
        yield sprintf "%i[if]" me
        yield! linkNext me (prettyMermaidExpr c)
        yield! linkNext me (prettyMermaidExpr t)
        yield! linkNext me (prettyMermaidExpr f)
    | EOp (l, op, r) ->
        yield sprintf "%i[\"%s\"]" me (prettyOp op)
        yield! linkNext me (prettyMermaidExpr l)
        yield! linkNext me (prettyMermaidExpr r)
    | EGroup ([v, e], b) ->
        yield sprintf "%i[\"rec %s\"]" me v
        yield! linkNext me (prettyMermaidExpr e)
        yield! linkNext me (prettyMermaidExpr b)
    | ETuple ls ->
        yield sprintf "%i[tuple]" me
        for a in ls do
            yield! linkNext me (prettyMermaidExpr a)
    | EMatch (e, cases) ->
        yield sprintf "%i[match]" me
        yield! linkNext me (prettyMermaidExpr e)
        for (p, b) in cases do
            yield! linkNext me (prettyMermaidExpr b)
    | EGroup (a, b) ->
        yield sprintf "%i[rec]" me
        for (v, e) in a do
            yield! linkNext me (prettyMermaidExpr e)
        yield! linkNext me (prettyMermaidExpr b)
    | ERaw (_, s) ->
        yield sprintf "%i[\"%s\"]" me s
}

let prettyMermaidDecl ast : MermaidM<string> = mermaid {
    do! bumpIdx
    let! me = getIdx
    match ast.kind with
    | DExpr e ->
        yield! prettyMermaidExpr e
    | DLet (v, b) ->
        yield sprintf "%i[\"let %s\"]" me (prettyPattern v)
        yield! linkNext me (prettyMermaidExpr b)
    | DGroup [v, b] ->
        yield sprintf "%i[\"let %s\"]" me v
        yield! linkNext me (prettyMermaidExpr b)
    | _ ->
        yield ""
}

let prettyMermaidDecls asts : MermaidM<string> =
    let rec cont (asts: seq<DeclRaw<'t, 'u>>) : MermaidM<string> = mermaid {
        for a in asts do
            yield! prettyMermaidDecl a
    }
    mermaid {
        yield "graph TD"
        yield! cont asts
    }

let startMermaidPopup mermaid =
    $"{{
        \"code\": \"{System.Web.HttpUtility.JavaScriptStringEncode mermaid}\",
        \"mermaid\": {{
            \"theme\": \"dark\"
        }},
        \"autoSync\": \"false\",
        \"updateDiagram\": \"true\"
    }}"
    |> System.Text.Encoding.UTF8.GetBytes
    |> System.Convert.ToBase64String
    |> fun s ->
        let mutable proc = System.Diagnostics.ProcessStartInfo()
        proc.FileName <- $"https://mermaid.live/view#base64:{s}"
        proc.UseShellExecute <- true
        System.Diagnostics.Process.Start proc