module Parse

open Util
open Combinator
open Common
open System
open System.Globalization

open Repr

// Helpers
let isAlpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let isNumeric c = (c >= '0' && c <= '9')
let isAlphaNumeric c = isAlpha c || isNumeric c || (c = '_')
let mkString = List.toArray >> String
let whitespaceP = many (oneOf [' '; '\r'; '\n'; '\t']) *> just ()
let whitespacedP p = between whitespaceP p whitespaceP
let parens p = whitespacedP (between (one '(') p (one ')'))
let optParens p = parens p <|> whitespacedP p

let sepBy2 (p: Com<'T, 'S>) (sep: Com<'U, 'S>) : Com<'T list, 'S> =
    p <+> (sep *> p) <+> many (sep *> p)
    |>> fun ((a, b), c) -> a :: b :: c

// Operators
let operatorP = com {
    let! l = item
    let! r = look
    match l, r with
    | '!', '=' -> return! item *> just NotEq
    | '>', '=' -> return! item *> just GreaterEq
    | '<', '=' -> return! item *> just LessEq
    | '&', '&' -> return! item *> just And
    | '|', '|' -> return! item *> just Or
    | '=', _ -> return Equal
    | '>', _ -> return Greater
    | '<', _ -> return Less
    | '+', _ -> return Plus
    | '-', _ -> return Minus
    | '*', _ -> return Star
    | '/', _ -> return Slash
    | '%', _ -> return Modulo
    | _ -> return! fail()
}
let specificOperatorP op =
    guard ((=) op) operatorP
    |> attempt
    |> whitespacedP

// Identifiers
let identP = 
    eatWhile1 isAlphaNumeric
    |>> mkString
    |> whitespacedP

let keywordP target = 
    guard ((=) target) identP
    |> attempt

let reserved = Set.ofList [
    "in"; "let"; "true"; "false"
    "if"; "then"; "else"; "fn"
    "rec"; "sum"; "match"; "with"
    "int"; "bool"; "float"; "string";
    "void"; "unit"; "class"; "this"
    "of"; "member"
    ]

let notKeywordP : Com<string, char> =
    identP
    |> guard (fun x -> not <| Set.contains x reserved)

// Literals
let floatP = 
    eatWhile (fun x -> isNumeric x || x = '.')
    |>> mkString
    |> guard (fun x -> x.Contains ".")
    >>= fun s -> let (succ, num) =
                     Double.TryParse (s, NumberStyles.Any, CultureInfo.InvariantCulture)
                 if succ then num |> LFloat |> just
                 else fail()

let intP = 
    eatWhile (fun x -> isNumeric x)
    |>> mkString
    >>= fun s -> let (succ, num) =
                     Int32.TryParse (s, NumberStyles.Any, CultureInfo.InvariantCulture)
                 if succ then num |> LInt |> just
                 else fail()

let boolP =
    keywordP "true" *> just (LBool true)
    <|> keywordP "false" *> just (LBool false)

let stringP =
    within (one '"') (eatWhile ((<>) '"'))
    |>> mkString
    |>> LString

let charP =
    within (one ''') item
    |>> LChar

let literalP =
    (attempt (one '(' *> one ')' *> just LUnit))
    <|> stringP
    <|> boolP
    <|> attempt floatP
    <|> intP
    <|> charP
    |> whitespacedP

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
    parens (sepBy2 patP (one ','))
    |>> PTuple

patPImpl :=
    patTupleP <|> patNonTupleP

let groupP =
    parens (sepBy1 exprP (one ','))
    |>> fun s ->
        if List.length s > 1 then ETuple s
        else List.head s

let varP =
    notKeywordP
    |> attempt
    |>> EVar

let lamP =
    between (one '[') patP (one ']')
    <+> exprP
    |>> ELam

let letP =
    keywordP "let" *> patP <* one '=' <* whitespaceP
    <+> exprP <* keywordP "in" <* whitespaceP
    <+> exprP
    |>> (fun ((a, b), c) -> ELet (a, b, c))

let matchP =
    keywordP "match" *> exprP <* keywordP "with" <* opt (one '|')
    <+> sepBy1 (patP <* one '-' <* one '>' <+> exprP) (one '|')
    |>> EMatch

let ifP =
    keywordP "if" *> exprP
    <+> keywordP "then" *> exprP
    <+> keywordP "else" *> exprP
    |>> (fun ((a, b), c) -> EIf (a, b, c))

let recP =
    keywordP "rec" *>
    exprP
    |>> ERec

let opFunP =
    (operatorP
    |>> fun op -> ELam (PName "x", ELam (PName "y", EOp (EVar "x", op, EVar "y"))))
    |> whitespacedP
    |> parens
    |> attempt

let nonAppP =
    opFunP
    <|> (literalP |>> ELit)
    <|> groupP
    <|> varP
    |> whitespacedP

let appP =
    lamP
    <|> letP
    <|> matchP
    <|> recP
    <|> ifP
    <|> chainL1 nonAppP (just (curry EApp))

let specificBinOpP op =
  specificOperatorP op
  *> just (curry <| fun (l, r) -> EOp (l, op, r))
let chooseBinOpP = List.map (specificBinOpP) >> choice

let termP = appP
let mulDivP = chainL1 termP (chooseBinOpP [Star; Slash; Modulo])
let addSubP = chainL1 mulDivP (chooseBinOpP [Plus; Minus])
let comparisonP = chainL1 addSubP (chooseBinOpP [GreaterEq; LessEq; Greater; Less; NotEq; Equal])
let boolOpP = chainL1 comparisonP (chooseBinOpP [And; Or])

let unOpP = 
    (specificOperatorP Minus)
    <+> exprP
    |>> fun (_, e) -> EOp (EOp (e, Minus, e), Minus, e)

exprPImpl := whitespacedP (boolOpP <|> unOpP)

// User types
let typeP, typePImpl = declParser()

let typeVarP = 
    one ''' *> notKeywordP

let primTypeP =
    (typeVarP |>> TVar)
    <|> (choice (List.map keywordP ["int"; "bool"; "float"; "string"; "void"; "unit"]) |>> TConst)
    <|> (keywordP "this" *> just (TVar "this"))

let typeTermP =
    (attempt <| notKeywordP <+> many typeP |>> (fun (name, lst) -> TCtor (KSum name, lst)))
    <|> primTypeP
    <|> parens typeP
    |> whitespacedP

let productP =
    sepBy2 typeTermP (one '*')
    |>> fun lst -> TCtor (KProduct, lst)
    |> attempt

let arrowP =
    chainR1 (productP <|> typeTermP) (one '-' *> one '>' *> just (curry TArrow))

typePImpl := whitespacedP arrowP

// Declarations
let declLetP =
    keywordP "let" *>
    (patP)
    <* one '=' <* whitespaceP
    <+> exprP
    <* keywordP "in"
    |>> DLet

let declSumP =
    (keywordP "sum" *> notKeywordP
    <+> (many typeVarP) <* one '=' <* whitespaceP <* opt (one '|'))
    <+> (sepBy1 (notKeywordP <+> typeP) (one '|'))
    <* opt (keywordP "in")
    |>> (fun ((a,b),c) -> DUnion (a,b,c))

let declClassP = // TODO: Requirements
    (keywordP "class" *> notKeywordP <* one '=' <* whitespaceP <* opt (one '|'))
    <+> (sepBy1 (notKeywordP <* one ':' <+> typeP) (one '|'))
    <* opt (keywordP "in")
    |>> (fun (a, b) -> DClass (a, [], b) )

let declImplP = // TODO: Blanket impls
    (keywordP "member" *> typeP <* keywordP "of")
    <+> (notKeywordP <* one '=' <* whitespaceP <* opt (one '|'))
    <+> (sepBy1 (notKeywordP <* (one ':') <+> exprP) (one '|'))
    <* opt (keywordP "in")
    |>> (fun (a, b) -> DMember ([],flip a,b))

let declExprP =
    exprP |>> DExpr

let declP =
    (attempt declExprP) <|> declLetP <|> declSumP <|> declClassP <|> declImplP

let programP =
    many declP

let removeComments (txt: string) =
    txt.Split('\n')
    |> Array.map (fun s -> s.Trim())
    |> Array.filter (fun s -> not <| s.StartsWith("//"))
    |> String.concat "\n"

let parseDecl txt =
    txt
    |> removeComments
    |> mkMultiLineParser
    |> declP
    |> fst

let parseProgram txt =
    txt
    |> removeComments
    |> mkMultiLineParser
    |> programP
    |> fst
