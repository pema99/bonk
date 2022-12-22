module CodeGen

open System.IO
open Repr
open ReprUtil
open Lower
open Prelude

// JS AST
type JsBlock = JsStmt list

and JsStmt =
    | JsIf of JsExpr * JsBlock * JsBlock option
    | JsWhile of JsExpr * JsBlock
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

// Poor mans optimization passes
let rec traverseExpr fe fs (ex: JsExpr) : JsExpr =
    match ex with
    | JsDefer stm -> JsDefer (traverseStmt fe fs stm)
    | JsFunc (x, e) -> JsFunc (x, List.map (traverseStmt fe fs) e)
    | JsCall (f, e) -> JsCall (traverseExpr fe fs f, traverseExpr fe fs e)
    | JsOp (l, op, r) -> JsOp (traverseExpr fe fs l, op, traverseExpr fe fs r)
    | JsLet (x, e1, e2) -> JsLet (x, traverseExpr fe fs e1, traverseExpr fe fs e2)
    | JsList lst -> JsList (List.map (traverseExpr fe fs) lst)
    | JsObject lst -> JsObject (List.map (fun (a,b) -> a, traverseExpr fe fs b) lst)
    | JsField (e, x) -> JsField(traverseExpr fe fs e, x)
    | JsIndex (e, i) -> JsIndex(traverseExpr fe fs e, i)
    | _ -> ex
    |> fe

and traverseStmt fe fs (stm: JsStmt) : JsStmt =
    match stm with
    | JsIf (cond, tr, fl) -> JsIf (traverseExpr fe fs cond, List.map (traverseStmt fe fs) tr, Option.map (List.map (traverseStmt fe fs)) fl)
    | JsWhile (cond, body) -> JsWhile (traverseExpr fe fs cond, List.map (traverseStmt fe fs) body)
    | JsSwitch (sw, cases) -> JsSwitch (traverseExpr fe fs sw, List.map (fun (a,b) -> a, List.map (traverseStmt fe fs) b) cases)
    | JsDecl (x, e) -> JsDecl (x, traverseExpr fe fs e)
    | JsAssign (x, e) -> JsAssign (x, traverseExpr fe fs e)
    | JsReturn e -> JsReturn (traverseExpr fe fs e)
    | JsIgnore e -> JsIgnore (traverseExpr fe fs e)
    | JsScope lst -> JsScope (List.map (traverseStmt fe fs) lst)
    |> fs

// Pretty printing
let genIndent i =
    List.init i (fun _ -> "    ") |> String.concat ""

let rec pprJsExpr (i: int) (expr: JsExpr) : string =
    let ids = genIndent i
    match expr with
    | JsDefer (stmt) -> sprintf "(() => {\n%s%s})()" (pprJsStmt (i+1) stmt) ids
    | JsFunc (x, e) -> sprintf "((%s) => {\n%s%s})" x (pprJsBlock (i+1) e) ids
    | JsVar (v) -> v
    | JsCall (f, e) -> sprintf "%s(%s)" (pprJsExpr i f) (pprJsExpr i e)
    | JsConst (v) -> v
    | JsOp (l, op, r) -> sprintf "(%s %s %s)" (pprJsExpr i l) op (pprJsExpr i r)
    | JsLet (x, e1, e2) -> sprintf "const %s = %s;\n%s%s" (x) (pprJsExpr i e1) ids (pprJsExpr i e2)
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
    | JsWhile (cond, body) ->
        let cond = pprJsExpr i cond
        let body = pprJsBlock (i + 1) body
        sprintf "%swhile (%s) {\n%s%s}\n" ids cond body ids
    | JsScope (block) ->
        pprJsBlock i block
    | JsSwitch (oper, cases) ->
        let oper = pprJsExpr i oper
        let cases = 
            List.map (fun (case, block) -> 
                let inner = pprJsBlock (i+2) block
                sprintf "%scase %s: {\n%s%s} break;\n" ids2 case inner ids2
                ) cases
            |> String.concat ""
        sprintf "%sswitch (%s) {\n%s%s}\n" ids oper cases ids
    | JsDecl (x, e) ->
        sprintf "%slet %s = %s;\n" ids x (pprJsExpr i e)
    | JsAssign (x, e) ->
        sprintf "%s%s = %s;\n" ids x (pprJsExpr i e)
    | JsReturn (ret) ->
        sprintf "%sreturn %s;\n" ids (pprJsExpr i ret)
    | JsIgnore (expr) ->
        sprintf "%s%s;\n" ids (pprJsExpr i expr)

// Hoist variables from a pattern
let rec hoist pat =
    match pat with
    | PName a -> [a]
    | PTuple ps -> List.collect hoist ps
    | PUnion (_, p) -> hoist p
    | _ -> []

// Does an expression contain a speficic function call
let rec containsCall (name: string) (ex: TypedExpr) : bool =
    match ex.kind with
    | ELit (v)           -> false
    | EVar (a)           -> false
    | EApp ({ kind = EVar n }, x) when n = name -> true
    | EApp (f, x)        -> containsCall name f || containsCall name x
    | ELam (x, e)        -> containsCall name e
    | ELet (x, e1, e2)   -> containsCall name e1 || containsCall name e2
    | EIf (cond, tr, fl) -> containsCall name cond || containsCall name tr || containsCall name fl
    | EOp (l, op, r)     -> containsCall name l || containsCall name r
    | ETuple (es)        -> List.exists (containsCall name) es
    | EMatch (e, bs)     -> List.exists (containsCall name) (List.map snd bs)
    | EGroup (bs, rest)  -> List.exists (snd >> containsCall name) bs || containsCall name rest
    | ERaw _             -> false

// Is a function tail recursive given its name (all recursive calls in tail position)
let rec isTailRecursive (name: string) (ex: TypedExpr) : bool =
    match ex.kind with
    | ELit (v)           -> true
    | EVar (a)           -> true
    | EApp ({ kind = EVar n }, x) when n = name -> not (containsCall name x)
    | EApp (f, x)        -> isTailRecursive name f && not (containsCall name x)
    | ELam (x, e)        -> isTailRecursive name e
    | ELet (x, e1, e2)   -> isTailRecursive name e2 && not (containsCall name e1)
    | EIf (cond, tr, fl) -> isTailRecursive name tr && isTailRecursive name fl && not (containsCall name cond)
    | EOp (l, op, r)     -> not (containsCall name l) && not (containsCall name r)
    | ETuple (es)        -> List.forall (containsCall name >> not) es
    | EMatch (e, bs)     -> List.forall (isTailRecursive name) (List.map snd bs) && not (containsCall name e)
    | EGroup (bs, rest)  -> isTailRecursive name rest && not (List.exists (snd >> containsCall name) bs)
    | ERaw _                 -> true

// Emit a literal
let emitLit (lit: Literal) : string =
    match lit with
    | LFloat v -> string v
    | LString v -> sprintf "\"%s\"" v
    | LInt v -> string v
    | LBool v -> (string v).ToLower()
    | LChar v -> sprintf "\'%c\'.charCodeAt(0)" v
    | LUnit -> "\"<unit>\""

// Emit a pattern
let rec emitPat (pat: Pattern) : string =
    match pat with
    | PName x -> x
    | PTuple x -> sprintf "[%s]" (List.map emitPat x |> String.concat ", ")
    | PConstant x -> emitLit x
    | _ -> failwith "TODO PAT"

// Emit a binary operation
let emitOp ((preds, typ): QualType) (op: BinOp) (l: JsExpr) (r: JsExpr) : JsExpr =
    match op with
    | Plus      -> JsOp (l, "+", r)
    | Minus     -> JsOp (l, "-", r)
    | Star      -> JsOp (l, "*", r)
    | Modulo    -> JsOp (l, "%", r)
    | Equal     -> JsOp (l, "===", r)
    | NotEq     -> JsOp (l, "!==", r)
    | GreaterEq -> JsOp (l, ">=", r)
    | LessEq    -> JsOp (l, "<=", r)
    | Greater   -> JsOp (l, ">", r)
    | Less      -> JsOp (l, "<", r)
    | BoolAnd   -> JsOp (l, "&&", r)
    | BoolOr    -> JsOp (l, "||", r)
    | Slash ->
        if typ = tInt then 
            JsOp(JsOp (l, "/", r), "|", JsConst "0")
        else 
            JsOp (l, "/", r)

let optimizeTailRecursion (name: string) (arity: int) (ex: JsExpr) : JsExpr =
    // Grab parameter names
    let rec getParams ex =
        match ex with
        | JsFunc (xs, [ JsReturn (JsFunc (n1, n2)) ]) ->
            xs :: getParams (JsFunc (n1, n2))
        | JsFunc (xs, _) ->
            [xs]
        | _ ->
            []
    let parms = getParams ex
    if List.length parms <> arity then
        ex
    else
        // Grab parameters from a suspected tail call
        let getTailCallsParams ex =
            let rec unfoldTailCall ex =
                match ex with
                | JsCall (f, x) -> unfoldTailCall f |> Option.map (fun xs -> x :: xs)
                | JsVar (x) when x = name -> Some []
                | _ -> None
            match unfoldTailCall ex with
            | Some es when List.length es = arity -> Some es
            | _ -> None
        // Inject mutables into the function body for each tail call
        let rec injectMuts ex =
            traverseStmt ( // TODO: Needs to be a fold to handle shadowing
                function
                | JsCall (f, x) as e ->
                    match getTailCallsParams e with
                    | Some es ->
                        let lhs = sprintf "[%s]" (parms |> String.concat ", ")
                        let rhs = 
                            es
                            |> List.rev
                            |> JsList
                        JsDefer (JsScope [JsAssign (lhs, rhs)])
                    | None -> e
                | e -> e) id ex
        // Inject something into the function body while matching
        let rec injectMatch f ex =
            match ex with
            | JsFunc (x, [JsReturn (e)]) ->
                let rest =
                    match e with
                    | JsFunc (_, _) ->
                        [JsReturn (injectMatch f e)]
                    | JsDefer blk ->
                        f blk
                    | a ->
                        [JsIgnore a]
                JsFunc (x, rest)
            | ex -> ex
        injectMatch (fun inner -> [
            JsWhile (JsConst "true", [
                injectMuts inner
            ])
        ]) ex

// Emit an expression
let rec emitExpr (ex: TypedExpr) : JsExpr =
    match ex.kind with
    | ELit (lit) ->
        JsConst (emitLit lit)
    | EVar (a) ->
        JsVar a
    | EApp (f, x) ->
        JsCall (emitExpr f, emitExpr x)
    | ELam (x, e) ->
        match x with
        | PName x -> JsFunc (x, [JsReturn (emitExpr e)])
        | x ->
            let fvName = "__tmp"
            let hoisted = hoist x
            let matcher = emitPatternMatch (JsScope []) x ({ kind = EVar fvName; span = dummySpan; data = (Set.empty, tVoid) }) false
            JsFunc (fvName, 
                List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @ [
                    matcher
                    JsReturn (emitExpr e)
                ])
    | ELet (x, e1, e2) ->
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
            let matcher = emitPatternMatch (JsScope []) x e1 false
            JsDefer (
                JsScope (
                    List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                    [ matcher ] @
                    [ JsReturn (emitExpr e2) ]
                )
            )
    | EIf (cond, tr, fl) -> 
        JsDefer (JsIf (emitExpr cond, [JsReturn (emitExpr tr)], Some [JsReturn (emitExpr fl)]))
    | EOp (l, op, r) ->
        emitOp (ex.data) op (emitExpr l) (emitExpr r)
    | ETuple (es) ->
        JsList (List.map (emitExpr) es)
    | EMatch (e1, bs) ->
        let hoisted = List.collect (fun (p, _) -> hoist p) bs |> List.distinct
        let beg = List.mapi (fun i (p, _) -> emitPatternMatch (JsAssign ("_matched", JsConst (string i))) p e1 true) bs
        let sw = JsSwitch (JsVar "_matched", List.mapi (fun i (_, e) -> string i, [ JsReturn (emitExpr e) ]) bs)
        JsDefer (
            JsScope (
                List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                [ JsDecl ("_matched", JsConst "null") ] @
                beg @
                [sw]
            )
        )
    | EGroup ([x, i], rest) ->
        JsDefer (
            JsScope (
                [ JsDecl (x, emitOptimizedFuncDef x i)
                  JsReturn (emitExpr rest)
                ]
            )
        )
    | EGroup (bs, rest) ->
        let emitted = List.map (fun (name, body) -> JsDecl (name, emitExpr body)) bs
        JsDefer (
            JsScope (
                emitted @
                [ JsReturn (emitExpr rest) ]
            )
        )
    | ERaw (_, body) ->
        JsVar body

// Emit a structure that matches a pattern and adds bindings as necessary
// TODO: Optimize the constant re-scoping a bit
and emitPatternMatch (res: JsStmt) (pat: Pattern) (expr: TypedExpr) (hasAlternatives: bool) : JsStmt =
    let rec cont pat expr next =
        match pat with
        | PName a -> // name matches with anything // TODO: Don't use hardcoded match name, generate a unique one
            if hasAlternatives then
                JsIf (JsOp (JsVar "_matched", "===", JsConst "null" ),
                    [ JsAssign (a, expr)
                      next
                    ],
                    None)
            else
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

and emitOptimizedFuncDef (name: string) (ex: TypedExpr) : JsExpr =
    let rec getArity ex =
        match ex with
        | ELam (x, e) -> 1 +  getArity e.kind
        | _ -> 0
    let arity = getArity ex.kind
    let res = emitExpr ex
    if isTailRecursive name ex
    then optimizeTailRecursion name arity res
    else res

let eliminateReturnDefer stm =
    match stm with
    | JsReturn (JsDefer e) -> e
    | _ -> stm

let optimizeExpr = traverseExpr id eliminateReturnDefer
let optimizeStmt = traverseStmt id eliminateReturnDefer

// Emit a top level declaration
let emitDecl (d: TypedDecl) : JsStmt list =
    let res = 
        match d.kind with
        | DExpr e ->
            [JsIgnore (emitExpr e)]

        | DLet (x, e) ->
            match x with
            | PName x ->
                [ JsDecl (x, emitExpr e) ]
            | x ->
                let hoisted = hoist x
                let matcher = emitPatternMatch (JsScope []) x e false
                List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                [ matcher ]

        | DGroup ([x, i]) ->
            [ JsDecl (x, emitOptimizedFuncDef x i) ]

        | DGroup (bs) ->
            List.map (fun (name, body) -> JsDecl (name, emitExpr body)) bs

        | DUnion (name, typs, cases) ->
            let case n =
                JsDecl (n, 
                    JsFunc ("v", 
                        [JsReturn (
                            JsObject (["tag", JsConst ("\""+n+"\""); "val", JsVar "v"]))]))
            List.map (fun (n, _) -> case n) cases
        
        | DClass (name, reqs, mems) ->
            [JsIgnore (JsVar "// TODO TYPECLASS")]
        
        | DMember (blankets, pred, impls) ->
            List.map (fun (name, body) ->
                let mangled = mangleOverload name (getExprType body)
                JsDecl (mangled, emitExpr body)) impls
    List.map (optimizeStmt) res

let emitProgram (decls: TypedDecl list) =
    let jsAst = List.collect emitDecl decls
    let jsOutput = pprJsBlock 0 jsAst
    let jsOutput = jsInstrincs + jsOutput
    jsOutput