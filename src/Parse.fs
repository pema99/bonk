module Parse

open Util
open Combinator
open Common
open System
open System.Globalization

open Repr
open Lex

// Helpers
let tok tar = satisfy (fst >> (=) tar)
let parens p =  between (tok LParen) p (tok RParen)
let optParens p = parens p <|> p

let constructSpan ((_, (start, _)): Spanned<'t>) ((_, (_, stop)): Spanned<'t>) : Span =
    (start, stop)

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
    let spanned = (res, constructSpan start stop)
    return spanned
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
let typeDescP = extract (function (TypeDesc v, _) -> Some v | _ -> None)

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

// Expressions
let exprP, exprPImpl = declParser()

let groupP =
    spannedP (parens (sepBy1 exprP (tok Comma)))
    |>> fun (s, sp) ->
        if List.length s > 1 then (ETuple s, sp)
        else List.head s

let varP =
    identP
    |> attempt
    |>> EVar
    |> spannedP

let lamP =
    between (tok LBrack) patP (tok RBrack)
    <+> exprP
    |>> ELam
    |> spannedP

let letGroupP =
    ((tok Rec *> identP <* opP Equal) <+> exprP) <+>
    (many (tok And *> identP <* opP Equal <+> exprP))
    <* tok In
    <+> exprP
    |>> fun ((a,b),c) ->
        EGroup (a::b,c)
    |> spannedP

let letP =
    (tok Let) 
    *> (patP) <* opP Equal
    <+> exprP <* tok In
    <+> exprP
    |>> (fun ((a, b), c) ->
        ELet (a, b, c))
    |> spannedP

let matchP =
    tok Match *> exprP <* tok With <* opt (tok Pipe)
    <+> sepBy1 (patP <* tok Arrow <+> exprP) (tok Pipe)
    |>> EMatch
    |> spannedP

let ifP =
    tok If *> exprP
    <+> tok Then *> exprP
    <+> tok Else *> exprP
    |>> (fun ((a, b), c) -> EIf (a, b, c))
    |> spannedP

let opFunP =
    (spannedP (parens (anyOpP))
    |>> fun (op, s) ->
        (ELam (PName "x",
            (ELam (PName "y",
                (EOp ((EVar "x", s), op, (EVar "y", s)), s)), s)), s))
    |> attempt

let nonAppP =
    opFunP
    <|> (literalP |>> ELit |> spannedP)
    <|> groupP
    <|> varP

let appP =
    lamP
    <|> letGroupP
    <|> letP
    <|> matchP
    <|> ifP
    <|> chainL1 nonAppP (just <| fun l r -> (EApp (l, r), constructSpan l r))

let specificBinOpP op =
    opP op
    *> just (curry <| fun (l, r) -> (EOp (l, op, r), constructSpan l r))
let chooseBinOpP = List.map (specificBinOpP) >> choice

let termP = appP
let mulDivP = chainL1 termP (chooseBinOpP [Star; Slash; Modulo])
let addSubP = chainL1 mulDivP (chooseBinOpP [Plus; Minus])
let comparisonP = chainL1 addSubP (chooseBinOpP [GreaterEq; LessEq; Greater; Less; NotEq; Equal])
let boolOpP = chainL1 comparisonP (chooseBinOpP [BoolAnd; BoolOr])

let unOpP = 
    (opP Minus)
    <+> exprP
    |>> fun (_, e) -> (EOp ((EOp (e, Minus, e), snd e), Minus, e), snd e)

exprPImpl := boolOpP <|> unOpP

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
    chainR1 (productP <|> typeTermP) (tok Arrow *> just (curry TArrow))

typePImpl := arrowP

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

let declImplP = // TODO: Blanket impls
    (tok Member *> typeP <* tok Of)
    <+> (identP <* opP Equal <* opt (tok Pipe))
    <+> (sepBy1 (identP <* (tok Colon) <+> exprP) (tok Pipe))
    <* opt (tok In)
    |>> (fun (a, b) -> DMember ([],flip a,b))

let declExprP =
    exprP |>> DExpr

let declP =
    (attempt declExprP) <|> declLetGroupP <|> declLetP <|> declSumP <|> declClassP <|> declImplP

let programP =
    many declP

let runParse (kind: Com<'t, Spanned<Token>>) txt =
    let lexed = lex txt
    match lexed with
    | Success v ->
        let res, state =
            v
            |> List.toArray
            |> mkArrayParser
            |> kind
        let state = state :?> ArrayCombinatorState<Spanned<Token>>
        match res with
        | Success v when state.Offset >= state.Toks.Length-1 -> ()
        | _ ->
            let (tok, span) = state.Toks.[max 0 <| min (state.Offset) (state.Toks.Length-1)]
            let line = fst (fst span)
            let col = snd (fst span)
            printfn "Parsing error at line %i, column %i: Unexpected token '%A'." line col tok 
        res
    | err -> copyFailure err

let parseDecl = runParse declP
let parseProgram = runParse programP
