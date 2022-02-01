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
let parens p = between (one '(') p (one ')')

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
    stringP
    <|> boolP
    <|> attempt floatP
    <|> intP
    |> whitespacedP

// Expressions
let exprP, exprPImpl = declParser()
let groupP = parens exprP

let reserved = Set.ofList [
    "in"; "let"; "true"; "false"
    "if"; "then"; "else"; "fn"
    "rec"
    ]

let varP =
    identP
    |> guard (fun x -> not <| Set.contains x reserved)
    |> attempt
    |>> Var

let patP =
    sepBy1 identP (one ',')
    |>> fun s ->
        if List.length s > 1 then PTuple s
        else PName (List.head s)

let lamP : Com<Expr, char> =
    between (one '[') patP (one ']')
    <+> exprP
    |>> Lam

let letP =
    keywordP "let" *> patP <* one '=' <* whitespaceP
    <+> exprP <* keywordP "in" <* whitespaceP
    <+> exprP
    |>> (fun ((a, b), c) -> Let (a, b, c))

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
    groupP
    <|> literalP
    <|> lamP
    <|> letP
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
  sepBy1 boolOpP (one ',')
  |> guard (fun s -> List.length s > 1)
  |>> Tup
  |> attempt

exprPImpl := whitespacedP (tupleP <|> boolOpP)

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