module Parse

open Util
open Combinator
open Common
open System
open System.Globalization

open Repr
open ReprUtil
open Lex

// Helpers
let tok tar = satisfy (fst >> (=) tar)
let parens p =  between (tok LParen) p (tok RParen)
let optParens p = parens p <|> p

let spanBetweenExprs (start: UntypedExpr) (stop: UntypedExpr) : Span =
    (fst start.span, snd stop.span)

let spannedP p : Com<Spanned<'t>, Spanned<Token>> = com {
    // Get token about to be parsed
    let! state = com.get()
    let state = state :?> ArrayCombinatorState<Spanned<Token>>
    let start = state.Toks.[min (state.Offset) (state.Toks.Length-1)]
    // Run parser
    let! res = p
    // Get token that was parsed last
    let! state = com.get()
    let state = state :?> ArrayCombinatorState<Spanned<Token>>
    let stop = state.Toks.[min (state.Offset-1) (state.Toks.Length-1)]
    // Construct span
    let (spanStart, _) = (snd start)
    let (_, spanEnd) = (snd stop)
    return (res, (spanStart, spanEnd))
}

let spannedExprP p : Com<UntypedExpr, Spanned<Token>> = com {
    let! res = spannedP p
    return mkExpr (fst res) (snd res)
}

let extract ex =
    satisfy (ex >> Option.isSome)
    |>> ex
    >>= function
        | Some x -> just x
        | _ -> fail()

let opP op    = extract (function (Op v, _) when v = op -> Some v | _ -> None)
let anyOpP    = extract (function (Op v, _) -> Some v | _ -> None)
let identP    = extract (function (Ident v, _) -> Some v | _ -> None)
let literalP  = extract (function (Lit v, _) -> Some v | _ -> None)
let stringP   = extract (function (Lit (LString v), _) -> Some v | _ -> None)
let typeDescP = extract (function (TypeDesc v, _) -> Some v | _ -> None)
let qualP     = extract (function (Qual v, _) -> Some v | _ -> None)

// Patterns
let patP, patPImpl = declParser()

let patUnionP =
    attempt (identP <+> patP |>> PUnion)

let patNameP =
    identP |>> PName

let patLiteralP =
    literalP |>> PConstant

let patNonTupleP =
    patUnionP <|> patLiteralP <|> patNameP

let patTupleP =
    parens (sepBy2 patP (tok Comma))
    |>> PTuple

patPImpl :=
    patTupleP <|> patNonTupleP

// User types
let typeP, typePImpl = declParser()

let typeVarP = 
    tok Tick *> identP

let primTypeP =
    (typeVarP |>> TVar)
    <|> typeDescP

let typeTermP =
    (attempt <| identP <+> many typeP |>> (fun (name, lst) -> TCtor (KSum name, lst)))
    <|> primTypeP
    <|> parens typeP

let productP =
    sepBy2 typeTermP (opP Star)
    |>> fun lst -> TCtor (KProduct, lst)
    |> attempt

let arrowP =
    chainR1 (productP <|> typeTermP) (tok Arrow *> just (fun a b -> TCtor (KArrow, [a;b])))

typePImpl := arrowP

// Expressions
let (exprP, exprPImpl) = declParser()

let groupP =
    spannedP (parens (sepBy1 exprP (tok Comma)))
    |>> fun (s, sp) ->
        if List.length s > 1 then mkExpr (ETuple s) sp
        else List.head s

let varP =
    identP
    |> attempt
    |>> EVar
    |> spannedExprP

let lamP =
    between (tok LBrack) patP (tok RBrack)
    <+> exprP
    |>> ELam
    |> spannedExprP

let letGroupP =
    ((tok Rec *> identP <* opP Equal) <+> exprP) <+>
    (many (tok And *> identP <* opP Equal <+> exprP))
    <* tok In
    <+> exprP
    |>> fun ((a,b),c) ->
        EGroup (a::b,c)
    |> spannedExprP

let letP =
    (tok Let) 
    *> (patP) <* opP Equal
    <+> exprP <* tok In
    <+> exprP
    |>> (fun ((a, b), c) ->
        ELet (a, b, c))
    |> spannedExprP

let matchP =
    tok Match *> exprP <* tok With <* opt (tok Pipe)
    <+> sepBy1 (patP <* tok Arrow <+> exprP) (tok Pipe)
    |>> EMatch
    |> spannedExprP

let ifP =
    tok If *> exprP
    <+> tok Then *> exprP
    <+> tok Else *> exprP
    |>> (fun ((a, b), c) -> EIf (a, b, c))
    |> spannedExprP

let opFunP =
    spannedP (parens (anyOpP))
    |>> fun (op, s) ->
        (mkExpr (ELam (PName "x",
            mkExpr (ELam (PName "y",
                mkExpr (EOp (mkExpr (EVar "x") s, op, mkExpr (EVar "y") s)) s)) s)) s)
    |> attempt

let listLiteralP =
    spannedP (between (tok LBrace) (sepBy exprP (tok Semicolon)) (tok RBrace))
    |>> fun (lst, span) ->
        lst
        |> List.rev
        |> List.fold
            (fun acc e ->
                mkExpr (EApp (
                    mkExpr (EVar "Cons") e.span, 
                        mkExpr (ETuple [mkExpr e.kind e.span; acc]) e.span)) e.span)
            (mkExpr (EApp (mkExpr (EVar "Nil") span, mkExpr (ELit LUnit) span)) span)

let nonAppP =
    opFunP
    <|> (literalP |>> ELit |> spannedExprP)
    <|> groupP
    <|> varP
    <|> listLiteralP

let appP = com {
    let! next = look
    match fst next with
    | LBrack -> return! lamP
    | Rec -> return! letGroupP
    | Let -> return! letP
    | Match -> return! matchP
    | If -> return! ifP
    | _ -> return! chainL1 nonAppP (just <| fun l r -> mkExpr (EApp (l, r)) (spanBetweenExprs l r))
}

let specificBinOpP op =
    opP op
    *> just (curry <| fun (l, r) -> mkExpr (EOp (l, op, r)) (spanBetweenExprs l r))
let chooseBinOpP = List.map (specificBinOpP) >> choice

let termP = appP
let mulDivP = chainL1 termP (chooseBinOpP [Star; Slash; Modulo])
let addSubP = chainL1 mulDivP (chooseBinOpP [Plus; Minus])
let comparisonP = chainL1 addSubP (chooseBinOpP [GreaterEq; LessEq; Greater; Less; NotEq; Equal])
let boolOpP = chainL1 comparisonP (chooseBinOpP [BoolAnd; BoolOr])

let pipeRightP =
    tok PipeRight
    *> just (curry <| fun (l, r) -> mkExpr (EApp (r, l)) (spanBetweenExprs l r))
let pipeLeftP =
    tok PipeLeft
    *> just (curry <| fun (l, r) -> mkExpr (EApp (l, r)) (spanBetweenExprs l r))
let pipeOpP = chainR1 (chainL1 boolOpP pipeRightP) pipeLeftP

let unOpP = 
    (opP Minus)
    <+> exprP
    |>> fun (_, e) -> mkExpr (EOp (mkExpr (EOp (e, Minus, e)) e.span, Minus, e)) e.span

let rawP =
    com {
        let! toks, body =
            extract (function (RawBlock (v, u), _) -> Some (v, u) | _ -> None)
        if Seq.isEmpty toks then
            return ERaw (None, body)
        else
            // Parser inner type in new context
            let typ =
                toks
                |> List.toArray
                |> mkArrayParser
                |> typeP
                |> fst
            match typ with
            | Success typ -> return ERaw (Some (Set.empty, typ), body)
            | _ -> return! fail()
    } |> spannedExprP

exprPImpl := pipeOpP <|> unOpP <|> rawP

// Declarations
let declLetP =
    (tok Let)
    *> (patP) 
    <* opP Equal
    <+> exprP
    <* tok In
    |>> DLet

let declLetGroupP =
    (tok Rec *> identP <* opP Equal <+> exprP) <+>
    (many (tok And *> identP <* opP Equal <+> exprP))
    <* tok In
    |>> fun ((a,b)) ->
        DGroup (a::b)

let declSumP =
    (tok Sum *> identP
    <+> (many typeVarP) <* opP Equal <* opt (tok Pipe))
    <+> (sepBy1 (identP <+> typeP) (tok Pipe))
    <* opt (tok In)
    |>> (fun ((a,b),c) -> DUnion (a,b,c))

let declClassP = // TODO: Requirements
    (tok Class *> identP <* opP Equal <* opt (tok Pipe))
    <+> (sepBy1 (identP <* tok Colon <+> typeP) (tok Pipe))
    <* opt (tok In)
    |>> (fun (a, b) -> DClass (a, [], b) )

let declImplP =
    (tok Member *> typeP <* tok Of)
    <+> (identP <* opP Equal <* opt (tok Pipe))
    <+> (sepBy1 (identP <* (tok Colon) <+> exprP) (tok Pipe))
    <* opt (tok In)
    |>> (fun (a, b) -> DMember (Set.empty,flip a,b))

let declExprP =
    exprP |>> DExpr

let qualifiersP =
    many qualP |>> Set.ofList

let declP =
    qualifiersP <+>
    (com {
        let! next = look
        match fst next with
        | Let -> return! declLetP
        | Rec -> return! declLetGroupP
        | Sum -> return! declSumP
        | Class -> return! declClassP
        | Member -> return! declImplP
        | _ -> return! declExprP
    })
    |> spannedP
    |>> fun ((quals, decl), span) -> {
            kind = decl;
            span = span;
            qualifiers = quals
            data = ()
        }

let importsP =
    many (tok Import *> stringP)

let programP =
    importsP *> (many declP)

let runParse (kind: Com<'t, Spanned<Token>>) allowMore txt =
    let lexed = lex allowMore txt
    match lexed with
    | Ok toks ->
        let res, state =
            toks
            |> List.toArray
            |> mkArrayParser
            |> kind
        let state = state :?> ArrayCombinatorState<Spanned<Token>>
        match res with
        | Success v when (state.Offset >= state.Toks.Length-1) || allowMore ->
            Ok v
        | _ ->
            let (tok, span) = state.Toks.[max 0 <| min (state.Offset) (state.Toks.Length-1)]
            Error (span, sprintf "Unexpected token '%A'." tok)
    | Error err -> Error err

let parseDecl = runParse declP false
let parseImports = runParse importsP true
let parseProgram = runParse programP false

let parsePrograms (programs: (string * string) list) : Result<UntypedProgram list, FileErrorInfo> =
    let filenames, contents = List.unzip programs
    let results = 
        List.map2
            (fun left right ->
                right
                |> Result.map (fun v -> left, v)
                |> Result.mapError (fun (sp, msg) -> { msg = msg; span = sp; file = left }))
            filenames
            (List.map parseProgram contents)
    match List.tryFind (function Error _ -> true | _ -> false) results with
    | Some (Error err) -> Error err
    | _ -> Ok (List.choose (function Error _ -> None | Ok v -> Some v) results)