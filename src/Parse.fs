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
  | '=', '=' -> return! item *> just Equal
  | '&', '&' -> return! item *> just And
  | '|', '|' -> return! item *> just Or
  | '>', _ -> return Greater
  | '<', _ -> return Less
  | '+', _ -> return Plus
  | '-', _ -> return Minus
  | '*', _ -> return Star
  | '/', _ -> return Slash
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
    "void"; "unit"
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
               if succ then num |> LFloat |> Lit |> just
               else fail()

let intP = 
  eatWhile (fun x -> isNumeric x)
  |>> mkString
  >>= fun s -> let (succ, num) =
                 Int32.TryParse (s, NumberStyles.Any, CultureInfo.InvariantCulture)
               if succ then num |> LInt |> Lit |> just
               else fail()

let boolP =
    keywordP "true" *> just (Lit (LBool true))
    <|> keywordP "false" *> just (Lit (LBool false))

let stringP =
    within (one '"') (eatWhile ((<>) '"'))
    |>> mkString
    |>> LString
    |>> Lit

let literalP =
    (attempt (one '(' *> one ')' *> just (Lit LUnit)))
    <|> stringP
    <|> boolP
    <|> attempt floatP
    <|> intP
    |> whitespacedP

// Expressions
let exprP, exprPImpl = declParser()
let groupP = parens exprP

// Patterns
let patP, patPImpl = declParser()

let patUnionP =
    attempt (identP <+> patP |>> PUnion)

let patNameP =
    identP |>> PName

let patNonTupleP =
    patUnionP <|> patNameP

let patTupleP =
    parens (sepBy2 patP (one ','))
    |>> PTuple

patPImpl :=
    patTupleP <|> patNonTupleP

let varP =
    notKeywordP
    |> attempt
    |>> Var

let lamP : Com<Expr, char> =
    between (one '[') patP (one ']')
    <+> exprP
    |>> Lam

let letP =
    keywordP "let" *> patP <* one '=' <* whitespaceP
    <+> exprP <* keywordP "in" <* whitespaceP
    <+> exprP
    |>> (fun ((a, b), c) -> Let (a, b, c))

let matchP =
    keywordP "match" *> exprP <* keywordP "with"
    <+> sepBy1 (patP <* one '.' <+> exprP) (one '|')
    |>> Match

let ifP =
    keywordP "if" *> exprP
    <+> keywordP "then" *> exprP
    <+> keywordP "else" *> exprP
    |>> (fun ((a, b), c) -> If (a, b, c))

let recP =
    keywordP "rec" *>
    exprP
    |>> Rec

let nonAppP =
    literalP
    <|> groupP
    <|> lamP
    <|> letP
    <|> matchP
    <|> recP
    <|> ifP
    <|> varP
    |> whitespacedP

let appP = 
    chainL1 nonAppP (just (curry App))

// TODO: Unop
(*let unOpP = 
  (specificOperatorP Plus <|> specificOperatorP Minus <|> specificOperatorP Not)
  <+> exprP // TODO: technically should be term
  |>> UnOp*)

let specificBinOpP op =
  specificOperatorP op
  *> just (curry <| fun (l, r) -> Op (l, op, r))
let chooseBinOpP = List.map (specificBinOpP) >> choice

let termP = appP
let mulDivP = chainL1 termP (chooseBinOpP [Star; Slash])
let addSubP = chainL1 mulDivP (chooseBinOpP [Plus; Minus])
let comparisonP = chainL1 addSubP (chooseBinOpP [GreaterEq; LessEq; Greater; Less; NotEq; Equal])
let boolOpP = chainL1 comparisonP (chooseBinOpP [And; Or])

let tupleP =
  sepBy2 boolOpP (one ',')
  |>> Tup
  |> attempt

// User types
let typeP, typePImpl = declParser()

let typeVarP = 
    one ''' *> notKeywordP

let primTypeP =
    (typeVarP |>> TVar)
    <|> (choice (List.map keywordP ["int"; "bool"; "float"; "string"; "void"; "unit"]) |>> TCon)

let typeTermP =
  (attempt <| notKeywordP <+> many typeP |>> (fun (name, lst) -> TCtor (KSum name, lst)))
  <|> primTypeP
  <|> parens typeP
  |> whitespacedP

let productP =
    sepBy2 typeTermP (one '*')
    |>> fun lst -> TCtor (KProduct (List.length lst), lst)
    |> attempt

let arrowP =
    chainL1 (productP <|> typeTermP) (one '-' *> one '>' *> just (curry TArr))

typePImpl := whitespacedP arrowP

let sumDeclP =
  (keywordP "sum" *> notKeywordP
  <+> (many typeVarP) <* one '=')
  <+> (sepBy1 (notKeywordP <+> typeP) (one '|'))
  <* keywordP "in" <+> exprP
  |>> (fun (((a,b),c),d) -> Sum (a,b,c,d))

exprPImpl := whitespacedP (sumDeclP <|> tupleP <|> boolOpP)

let parseProgram txt =
    mkMultiLineParser txt
    |> exprP
    |> fst

// Incomplete declarations for REPL
let declP =
    keywordP "let" *>
    (sepBy1 identP (one ','))
    <* one '=' <* whitespaceP
    <+> exprP

let replP =
    attempt (just [] <+> exprP) <|> declP

let parseRepl txt =
    mkMultiLineParser txt
    |> replP
    |> fst