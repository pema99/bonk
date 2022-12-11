module CodeGen

open System.IO
open Repr
open Parse
open Combinator
open Inference
open Prelude
open Lower

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
    match ex with
    | TELit (pt, v)           -> false
    | TEVar (pt, a)           -> false
    | TEApp (pt, TEVar (ty2, n), x) when n = name -> true
    | TEApp (pt, f, x)        -> containsCall name f || containsCall name x
    | TELam (pt, x, e)        -> containsCall name e
    | TELet (pt, x, e1, e2)   -> containsCall name e1 || containsCall name e2
    | TEIf (pt, cond, tr, fl) -> containsCall name cond || containsCall name tr || containsCall name fl
    | TEOp (pt, l, op, r)     -> containsCall name l || containsCall name r
    | TETuple (pt, es)        -> List.exists (containsCall name) es
    | TEMatch (pt, e, bs)     -> List.exists (containsCall name) (List.map snd bs)
    | TEGroup (pt, bs, rest)  -> List.exists (snd >> containsCall name) bs || containsCall name rest
    | TERaw (pt, v)           -> false

// Is a function tail recursive given its name (all recursive calls in tail position)
let rec isTailRecursive (name: string) (ex: TypedExpr) : bool =
    match ex with
    | TELit (pt, v)           -> true
    | TEVar (pt, a)           -> true
    | TEApp (pt, TEVar (ty2, n), x) when n = name -> not (containsCall name x)
    | TEApp (pt, f, x)        -> isTailRecursive name f && not (containsCall name x)
    | TELam (pt, x, e)        -> isTailRecursive name e
    | TELet (pt, x, e1, e2)   -> isTailRecursive name e2 && not (containsCall name e1)
    | TEIf (pt, cond, tr, fl) -> isTailRecursive name tr && isTailRecursive name fl && not (containsCall name cond)
    | TEOp (pt, l, op, r)     -> not (containsCall name l) && not (containsCall name r)
    | TETuple (pt, es)        -> List.forall (containsCall name >> not) es
    | TEMatch (pt, e, bs)     -> List.forall (isTailRecursive name) (List.map snd bs) && not (containsCall name e)
    | TEGroup (pt, bs, rest)  -> isTailRecursive name rest && not (List.exists (snd >> containsCall name) bs)
    | TERaw (pt, v)           -> true

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

// Emit a binary operator
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
    | BoolAnd -> "&&"
    | BoolOr -> "||"

// Emit an expression
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
            let matcher = emitPatternMatch (JsScope []) x (TEVar (([], tVoid), fvName)) false
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
            let matcher = emitPatternMatch (JsScope []) x e1 false
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
        JsList (List.map (emitExpr) es)
    | TEMatch (pt, ex, bs) ->
        match snd pt with
        | _ ->
            let hoisted = List.collect (fun (p, _) -> hoist p) bs |> List.distinct
            let beg = List.mapi (fun i (p, _) -> emitPatternMatch (JsAssign ("matched", JsConst (string i))) p ex true) bs
            let sw = JsSwitch (JsVar "matched", List.mapi (fun i (_, e) -> string i, [ JsReturn (emitExpr e) ]) bs)
            JsDefer (
                JsScope (
                    List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                    [ JsDecl ("matched", JsConst "null") ] @
                    beg @
                    [sw]
                )
            )
    | TEGroup (pt, [x, i], rest) when isTailRecursive x i -> 
        let optim = optimizeTailRecursion x i
        JsDefer (
            JsScope (
                [ JsDecl (x, optim)
                  JsReturn (emitExpr rest)
                ]
            )
        )
    | TEGroup (pt, bs, rest) ->
        let emitted = List.map (fun (name, body) -> JsDecl (name, emitExpr body)) bs
        JsDefer (
            JsScope (
                emitted @
                [ JsReturn (emitExpr rest) ]
            )
        )
    | TERaw (pt, body) ->
        JsVar body

// Instead of emitting a normal function, emit a trampolined version
// assuming the function is recusive. Input is the function name and expression.
and optimizeTailRecursion (name: string) (ex: TypedExpr) : JsExpr =
    // Get fun arity
    let rec getArity ex =
        match ex with
        | TELam (pt, x, e) -> 1 +  getArity e
        | _ -> 0
    let arity = getArity ex
    // Build an application chain for the trampoline
    let rec buildCall i ex =
        match ex with
        | TELam (pt, x, e) -> JsCall (buildCall (i+1) e, JsVar (sprintf "__arg%i" (arity-1-i)))
        | _ -> JsVar name
    // Inject something into the function body, use fresh names for args
    let rec inject f i ex =
        match ex with
        | TELam (pt, x, (TELam (_, _, _) as e)) ->
            JsFunc ((sprintf "__arg%i" i), [JsReturn (inject f (i+1) e)])
        | TELam (pt, x, e) -> 
            JsFunc ((sprintf "__arg%i" i), f)
        | ex -> emitExpr ex
    // Inject something into the function body while matching
    let rec injectMatch f ex =
        match ex with
        | TELam (pt, x, e) ->
            let rest =
                match e with
                | TELam (_, _, _) -> [JsReturn (injectMatch f e)]
                | e -> f e
            match x with
            | PName x -> JsFunc (x, rest)
            | x ->
                let fvName = "__tmp"
                let hoisted = hoist x
                let matcher = emitPatternMatch (JsScope []) x (TEVar (([], tVoid), fvName)) false
                JsFunc (fvName, 
                    List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @ [matcher] @ rest)
        | ex -> emitExpr ex
    // Create delayed lambda around function body
    let delayed = 
        injectMatch (fun inner -> [
            JsDecl ("__cont", JsFunc ("", [
                JsReturn (emitExpr inner)
            ]))
            JsAssign ("__cont.inner", JsConst "true")
            JsReturn (JsVar "__cont")
        ]) ex
    // Create trampoline
    inject ([
        JsDecl (name, delayed)
        JsDecl ("__rec", buildCall 0 ex)
        JsWhile (JsOp (JsField (JsVar "__rec", "inner"), "===", JsConst "true"),
            [ JsAssign("__rec", JsCall(JsVar "__rec", JsConst "")) ])
        JsReturn (JsVar "__rec")
    ]) 0 ex

// Emit a structure that matches a pattern and adds bindings as necessary
// TODO: Optimize the constant re-scoping a bit
and emitPatternMatch (res: JsStmt) (pat: Pattern) (expr: TypedExpr) (hasAlternatives: bool) : JsStmt =
    let rec cont pat expr next =
        match pat with
        | PName a -> // name matches with anything // TODO: Don't use hardcoded match name, generate a unique one
            if hasAlternatives then
                JsIf (JsOp (JsVar "matched", "===", JsConst "null" ),
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

let eliminateReturnDefer stm =
    match stm with
    | JsReturn (JsDefer e) -> e
    | _ -> stm

let optimizeExpr = traverseExpr id eliminateReturnDefer
let optimizeStmt = traverseStmt id eliminateReturnDefer

// Emit a top level declaration
let emitDecl (d: TypedDecl) : JsStmt list =
    let res = 
        match d with
        | TDExpr e ->
            [JsIgnore (emitExpr e)]

        | TDLet (x, e) ->
            match x with
            | PName x ->
                [ JsDecl (x, emitExpr e) ]
            | x ->
                let hoisted = hoist x
                let matcher = emitPatternMatch (JsScope []) x e false
                List.map (fun n -> JsDecl (n, JsConst "null")) hoisted @
                [ matcher ]

        | TDGroup (bs) ->
            List.map (fun (name, body) -> JsDecl (name, emitExpr body)) bs

        | TDUnion (name, typs, cases) ->
            let case n =
                JsDecl (n, 
                    JsFunc ("v", 
                        [JsReturn (
                            JsObject (["tag", JsConst ("\""+n+"\""); "val", JsVar "v"]))]))
            List.map (fun (n, _) -> case n) cases
        
        | TDClass (name, reqs, mems) ->
            [JsIgnore (JsVar "// TODO TYPECLASS")]
        
        | TDMember (blankets, pred, impls) ->
            List.map (fun (name, body) ->
                let mangled = mangleOverload name (getExprType body)
                JsDecl (mangled, emitExpr body)) impls
    List.map (optimizeStmt) res

let startCompile builtins stdlib files =
    let stdlib = if not builtins then false else stdlib
    let ast =
        files
        |> Seq.map (File.ReadAllText)
        |> String.concat "\n"
        |> fun str -> if stdlib then stdLib + str else str
        //|> fun str -> if builtins then jsInstrincs + str else str
        |> parseProgram
    let funSchemes = if builtins then funSchemes else Map.empty
    match ast with
    | Success decls ->
        let res, ((_,_,_,loc),_) = inferDecls decls ((funSchemes, Map.empty, classes, ((0,0),(0,0))), (Map.empty, 0))
        match res with
        | Ok decls ->
            let decls = lowerDecls decls
            let jsAst = List.collect emitDecl decls
            let jsOutput = pprJsBlock 0 jsAst
            let jsOutput = if builtins then jsInstrincs + jsOutput else jsOutput
            File.WriteAllText("out.js", jsOutput)
        | Error err -> printfn "Typing error(%A): %s" loc err
    | Failure -> printfn "Parsing error: Unknown"
    | FailureWith (err, loc) -> printfn "Parsing error (%A): %s" loc err
    | CompoundFailure errs -> Seq.iter (fun (err, loc) -> printfn "Parsing error (%A): %s" loc err) errs
    ()