module CodeGen

open Repr
open Monad
open Inference

type JsBlock = JsStmt list

and JsStmt =
    | JsIf of JsExpr * JsBlock * JsBlock option
    | JsSwitch of JsExpr * (string * JsBlock) list
    | JsDecl of string * JsExpr
    | JsAssign of string * JsExpr
    | JsReturn of JsExpr
    | JsIgnore of JsExpr
    | JsScope of JsBlock

and JsExpr =
    | JsDefer of JsStmt
    | JsFunc of string * JsBlock
    | JsVar of string
    | JsCall of JsExpr * JsExpr
    | JsConst of string
    | JsOp of JsExpr * string * JsExpr
    | JsLet of string * JsExpr * JsExpr
    | JsList of JsExpr list
    | JsObject of (string * JsExpr) list
    | JsField of JsExpr * string
    | JsIndex of JsExpr * int

let genIndent i =
    List.init i (fun _ -> "    ") |> String.concat ""

let rec pprJsExpr (i: int) (expr: JsExpr) : string =
    let ids = genIndent i
    match expr with
    | JsDefer (stmt) -> sprintf "(function() {\n%s%s})()" (pprJsStmt (i+1) stmt) ids
    | JsFunc (x, e) -> sprintf "function (%s) {\n%s%s}" x (pprJsBlock (i+1) e) ids
    | JsVar (v) -> v
    | JsCall (f, e) -> sprintf "%s(%s)" (pprJsExpr i f) (pprJsExpr i e)
    | JsConst (v) -> v
    | JsOp (l, op, r) -> sprintf "(%s %s %s)" (pprJsExpr i l) op (pprJsExpr i r)
    | JsLet (x, e1, e2) -> sprintf "var %s = %s;\n%s%s" (x) (pprJsExpr i e1) ids (pprJsExpr i e2)
    | JsList (lst) -> sprintf "[%s]" (lst |> List.map (pprJsExpr i) |> String.concat ", ")
    | JsObject (fields) -> sprintf "{ %s }" (List.map (fun (n, e) -> sprintf "%s: %s" n (pprJsExpr i e)) fields |> String.concat ", ")
    | JsField (e, f) -> sprintf "(%s).%s" (pprJsExpr i e) f
    | JsIndex (e, idx) -> sprintf "(%s)[%i]" (pprJsExpr i e) (idx)

and pprJsBlock (i: int) (block: JsBlock) : string =
    List.map (pprJsStmt i) block |> String.concat ""

and pprJsStmt (i: int) (stmt: JsStmt) : string =
    let ids = genIndent i
    let ids2 = genIndent (i+1)
    match stmt with
    | JsIf (cond, tr, fl) ->
        let cond = pprJsExpr i cond
        let trs = List.map (pprJsStmt (i + 1)) tr |> String.concat ""
        match fl with
        | Some fl ->
            let fls = List.map (pprJsStmt (i + 1)) fl |> String.concat ""
            sprintf "%sif (%s) {\n%s%s} else {\n%s%s}\n" ids cond trs ids fls ids
        | None ->
            sprintf "%sif (%s) {\n%s%s}\n" ids cond trs ids
    | JsScope (block) ->
        pprJsBlock i block
    | JsSwitch (oper, cases) ->
        let oper = pprJsExpr i oper
        let cases = 
            List.map (fun (case, block) -> 
                let inner = pprJsBlock (i+2) block
                sprintf "%scase %s: {\n%s%s}\n" ids2 case inner ids2
                ) cases
            |> String.concat ""
        sprintf "%sswitch (%s) {\n%s%s}\n" ids oper cases ids
    | JsDecl (x, e) ->
        sprintf "%svar %s = %s;\n" ids x (pprJsExpr i e)
    | JsAssign (x, e) ->
        sprintf "%s%s = %s;\n" ids x (pprJsExpr i e)
    | JsReturn (ret) ->
        sprintf "%sreturn %s;\n" ids (pprJsExpr i ret)
    | JsIgnore (expr) ->
        sprintf "%s%s;\n" ids (pprJsExpr i expr)

let rec hoist pat =
    match pat with
    | PName a -> [a]
    | PTuple ps -> List.collect hoist ps
    | PUnion (_, p) -> hoist p
    | _ -> []

let emitLit (lit: Lit) : string =
    match lit with
    | LFloat v -> string v
    | LString v -> sprintf "\"%s\"" v
    | LInt v -> string v
    | LBool v -> string v
    | LChar v -> sprintf "\'%c\'" v
    | LUnit -> "\"<unit>\""

let rec emitPat (pat: Pat) : string =
    match pat with
    | PName x -> x
    | PTuple x -> sprintf "[%s]" (List.map emitPat x |> String.concat ", ")
    | PConstant x -> emitLit x
    | _ -> failwith "TODO PAT"

let emitOp (op: BinOp) : string =
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Star -> "*"
    | Slash -> "/"
    | Modulo -> "%"
    | Equal -> "==="
    | NotEq -> "!=="
    | GreaterEq -> ">="
    | LessEq -> "<="
    | Greater -> ">"
    | Less -> "<"
    | And -> "&&"
    | Or -> "||"

let rec emitExpr (ex: TypedExpr) : JsExpr =
    match ex with
    | TELit (pt, lit) ->
        JsConst (emitLit lit)
    | TEVar (pt, a) ->
        JsVar a
    | TEApp (pt, f, x) ->
        JsCall (emitExpr f, emitExpr x)
    | TELam (pt, x, e) ->
        match x with
        | PName x -> JsFunc (x, [JsReturn (emitExpr e)])
        | x ->
            let fvName = "__tmp"
            let hoisted = hoist x
            let matcher = emitPatternMatch (JsScope []) x (TEVar (([], tVoid), fvName))
            JsFunc (fvName, 
                List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @ [
                    matcher
                    JsReturn (emitExpr e)
                ])
    | TELet (pt, x, e1, e2) ->
        match x with
        | PName x ->
            JsDefer (
                JsScope (
                    [ JsDecl (x, emitExpr e1)
                      JsReturn (emitExpr e2)
                    ]
                )
            )
        | x ->
            let hoisted = hoist x
            let matcher = emitPatternMatch (JsScope []) x e1
            JsDefer (
                JsScope (
                    List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                    [ matcher ] @
                    [ JsReturn (emitExpr e2) ]
                )
            )
    | TEIf (pt, cond, tr, fl) -> 
        JsDefer (JsIf (emitExpr cond, [JsReturn (emitExpr tr)], Some [JsReturn (emitExpr fl)]))
    | TEOp (pt, l, op, r) ->
        JsOp (emitExpr l, emitOp op, emitExpr r)
    | TETuple (pt, es) ->
        JsList (List.map emitExpr es)
    | TEMatch (pt, ex, bs) ->
        match snd pt with
        | _ ->
            let hoisted = List.collect (fun (p, _) -> hoist p) bs |> List.distinct
            let beg = List.mapi (fun i (p, _) -> emitPatternMatch (JsAssign ("matched", JsConst (string i))) p ex) bs
            let sw = JsSwitch (JsVar "matched", List.mapi (fun i (_, e) -> string i, [ JsReturn (emitExpr e) ]) bs)
            JsDefer (
                JsScope (
                    List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                    [ JsDecl ("matched", JsConst "0") ] @
                    beg @
                    [sw]
                )
            )
    | TERec (pt, e) ->
        match e with
        | TELam(ty, x, i) -> emitExpr i
        | _ -> emitExpr e

and emitPatternMatch (res: JsStmt) (pat: Pat) (expr: TypedExpr) : JsStmt =
    let rec cont pat expr next =
        match pat with
        | PName a -> // name matches with anything
            JsScope [
                JsAssign (a, expr)
                next
            ]
        | PConstant a ->
            JsIf (
                JsOp (JsConst (emitLit a), "===", expr),
                [ next ],
                None)
        | PTuple pats ->
            let rec nest pats idx =
                match pats with
                | h :: t -> cont h (JsIndex (expr, idx)) (nest t (idx+1))
                | [] -> next
            nest pats 0
        | PUnion (case, pat) ->
            JsIf (
                JsOp (JsField (expr, "tag"), "===", JsConst ("\""+case+"\"")),
                [ cont pat (JsField (expr, "val")) next ],
                None)
    cont pat (emitExpr expr) res


let emitDecl (d: TypedDecl) : JsStmt list =
    match d with
    | TDExpr e ->
        [JsIgnore (emitExpr e)]

    | TDLet (x, e) ->
        match x with
        | PName x ->
            [ JsDecl (x, emitExpr e) ]
        | x ->
            let hoisted = hoist x
            let matcher = emitPatternMatch (JsScope []) x e
            List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
            [ matcher ]

    | TDUnion (name, typs, cases) ->
        let case n =
            JsDecl (n, 
                JsFunc ("v", 
                    [JsReturn (
                        JsObject (["tag", JsConst ("\""+n+"\""); "val", JsVar "v"]))]))
        List.map (fun (n, _) -> case n) cases
    
    | TDClass (name, reqs, mems) ->
        [JsIgnore (JsVar "TODO TYPECLASS")]
    
    | TDMember (blankets, pred, exprs) ->
        [JsIgnore (JsVar "TODO TYPECLASS MEMBER")]
