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

// Expressions
let exprP, exprPImpl = declParser()

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

let groupP =
    parens (sepBy1 exprP (tok Comma))
    |>> fun s ->
        if List.length s > 1 then ETuple s
        else List.head s

let varP =
    identP
    |> attempt
    |>> EVar

let lamP =
    between (tok LBrack) patP (tok RBrack)
    <+> exprP
    |>> ELam

let letGroupP =
    ((tok Rec *> identP <* opP Equal) <+> exprP) <+>
    (many (tok And *> identP <* opP Equal <+> exprP))
    <* tok In
    <+> exprP
    |>> fun ((a,b),c) ->
        EGroup (a::b,c)

let letP =
    (tok Let) 
    *> (patP) <* opP Equal
    <+> exprP <* tok In
    <+> exprP
    |>> (fun ((a, b), c) ->
        ELet (a, b, c))

let matchP =
    tok Match *> exprP <* tok With <* opt (tok Pipe)
    <+> sepBy1 (patP <* tok Arrow <+> exprP) (tok Pipe)
    |>> EMatch

let ifP =
    tok If *> exprP
    <+> tok Then *> exprP
    <+> tok Else *> exprP
    |>> (fun ((a, b), c) -> EIf (a, b, c))

let opFunP =
    (anyOpP
    |>> fun op -> ELam (PName "x", ELam (PName "y", EOp (EVar "x", op, EVar "y"))))
    |> parens
    |> attempt

let nonAppP =
    opFunP
    <|> (literalP |>> ELit)
    <|> groupP
    <|> varP

let appP =
    lamP
    <|> letGroupP
    <|> letP
    <|> matchP
    <|> ifP
    <|> chainL1 nonAppP (just (curry EApp))

let specificBinOpP op =
  opP op
  *> just (curry <| fun (l, r) -> EOp (l, op, r))
let chooseBinOpP = List.map (specificBinOpP) >> choice

let termP = appP
let mulDivP = chainL1 termP (chooseBinOpP [Star; Slash; Modulo])
let addSubP = chainL1 mulDivP (chooseBinOpP [Plus; Minus])
let comparisonP = chainL1 addSubP (chooseBinOpP [GreaterEq; LessEq; Greater; Less; NotEq; Equal])
let boolOpP = chainL1 comparisonP (chooseBinOpP [BoolAnd; BoolOr])

let unOpP = 
    (opP Minus)
    <+> exprP
    |>> fun (_, e) -> EOp (EOp (e, Minus, e), Minus, e)

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

let parseDecl txt =
    let lexed = lex txt
    match lexed with
    | Success v ->
        v
        |> List.toArray
        |> mkArrayParser
        |> declP
        |> fst
    | err -> copyFailure err

let parseProgram txt =
    let lexed = lex txt
    match lexed with
    | Success v ->
        v
        |> List.toArray
        |> mkArrayParser
        |> programP
        |> fst
    | err -> copyFailure err
