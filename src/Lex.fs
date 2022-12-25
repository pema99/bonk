module Lex

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
let mkString = List.toArray >> System.String
let whitespaceP = many (oneOf [' '; '\r'; '\n'; '\t']) *> just ()
let whitespacedP p = between whitespaceP p whitespaceP

// Symbols
let operatorP = com {
    let! l = item
    let! r = opt look
    match l, r with
    | '!', Some '=' -> return! (item *> just NotEq) |>> Op
    | '>', Some '=' -> return! (item *> just GreaterEq) |>> Op
    | '<', Some '=' -> return! (item *> just LessEq) |>> Op
    | '&', Some '&' -> return! (item *> just BoolAnd) |>> Op
    | '|', Some '|' -> return! (item *> just BoolOr) |>> Op
    | '-', Some '>' -> return! (item *> just Arrow)
    | '<', Some '|' -> return! (item *> just PipeLeft)
    | '|', Some '>' -> return! (item *> just PipeRight)
    | '=', _ -> return Op Equal
    | '>', _ -> return Op Greater
    | '<', _ -> return Op Less
    | '+', _ -> return Op Plus
    | '-', _ -> return Op Minus
    | '*', _ -> return Op Star
    | '/', _ -> return Op Slash
    | '%', _ -> return Op Modulo
    | '(', _ -> return LParen
    | ')', _ -> return RParen
    | '[', _ -> return LBrack
    | ']', _ -> return RBrack
    | ',', _ -> return Comma
    | '|', _ -> return Pipe
    | ''', _ -> return Tick
    | ':', _ -> return Colon
    | ';', _ -> return Semicolon
    | '{', _ -> return LBrace
    | '}', _ -> return RBrace
    | _ -> return! fail()
    }

// Identifiers
let identP = 
    eatWhile1 isAlphaNumeric
    |>> mkString
    |> whitespacedP

let wordP =
    identP
    |>> function
        | "let"     -> Let
        | "in"      -> In
        | "if"      -> If
        | "then"    -> Then
        | "else"    -> Else
        | "sum"     -> Sum
        | "match"   -> Match
        | "with"    -> With
        | "member"  -> Member
        | "class"   -> Class
        | "of"      -> Of
        | "rec"     -> Rec
        | "and"     -> And
        | "import"  -> Import
        | "true"    -> Lit (LBool true)
        | "false"   -> Lit (LBool false)
        | "int"     -> TypeDesc (tInt)
        | "char"    -> TypeDesc (tChar)
        | "bool"    -> TypeDesc (tBool)
        | "float"   -> TypeDesc (tFloat)
        | "string"  -> TypeDesc (tString)
        | "void"    -> TypeDesc (tVoid)
        | "unit"    -> TypeDesc (tUnit)
        | "opaque"  -> TypeDesc (tOpaque)
        | "this"    -> TypeDesc (TVar "this")
        | "impure"  -> Qual (QImpure)
        | "memoize" -> Qual (QMemoize)
        | ident     -> Ident (ident)

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
    <|> attempt floatP
    <|> intP
    <|> attempt charP
    |>> Lit

// Comments
let commentP =
    one '/' *> one '/' *>
    eatWhile ((<>) '\n') *> one '\n'

// Put it all together
let spannedP p : Com<Spanned<'t>, char> = com {
    let! state = com.get()
    let state = state :?> MultiLineTextCombinatorState
    let start = (state.Line, state.Column)
    let! res = p
    let! state = com.get()
    let state = state :?> MultiLineTextCombinatorState
    let stop = (state.Line, state.Column)
    let spanned = (res, (start, stop))
    return spanned
}

let tokenP, tokenPImpl = declParser()

// Raw JS blocks
let rawBlockP =
    (one '$' *> many (tokenP) <* one '$')
    <+> (eatWhile ((<>) '$') |>> mkString)
    <* (one '$' *> one '$')
    |>> RawBlock

tokenPImpl :=
    many (attempt commentP <* whitespaceP) *>
    whitespacedP (spannedP (literalP <|> wordP <|> attempt operatorP <|> attempt rawBlockP))

let lex allowMore txt =
    let (res, state) = 
        txt
        |> mkMultiLineParser
        |> many (tokenP)
    let state = state :?> MultiLineTextCombinatorState
    match res with
    | Success v when (Seq.forall ((=) ';') (state.Source.Trim())) || allowMore -> Ok v
    | _ -> Error (((state.Line, state.Column), (0, 0)), "Lexing error")