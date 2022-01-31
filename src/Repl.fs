module Repl

open Repr
open Inference

// Eval
type Value =
    | VInt of int
    | VBool of bool
    | VFloat of float
    | VString of string
    | VClosure of string * Expr * TermEnv

and TermEnv = Map<string, Value>

let prettyValue v =
    match v with
    | VInt v -> string v
    | VBool v -> string v
    | VFloat v -> string v
    | VString v -> sprintf "%A" v
    | VClosure (a, _, _) -> sprintf "Closure@%s" a

let rec binop l op r =
    match l, op, r with
    | VInt l, Plus, VInt r -> VInt (l + r)
    | VInt l, Minus, VInt r -> VInt (l - r)
    | VInt l, Star, VInt r -> VInt (l * r)
    | VInt l, Slash, VInt r -> VInt (l / r)
    | VInt l, Equal, VInt r -> VBool (l = r)
    | _ -> failwith (sprintf "Unimplemented binop %A %A %A" l op r)

and eval tenv e =
    match e with
    | Lit (LInt v) -> Some (VInt v)
    | Lit (LBool v) -> Some (VBool v)
    | Lit (LFloat v) -> Some (VFloat v)
    | Lit (LString v) -> Some (VString v)
    | Op (l, op, r) ->
        let v1 = eval tenv l
        let v2 = eval tenv r
        match v1, v2 with
        | Some v1, Some v2 -> Some (binop v1 op v2)
        | _ -> None
    | Var a -> lookup tenv a
    | App (f, x) ->
        let clos = eval tenv f
        let arg = eval tenv x
        match clos, arg with
        | Some (VClosure (a, body, env)), Some v ->
            let nenv = extend env a v 
            eval nenv body
        | _ -> None
    | Lam (x, t) -> Some (VClosure (x, t, tenv))
    | Let (x, v, t) ->
        match eval tenv v with
        | Some ve ->
            let nenv = extend tenv x ve
            eval nenv t
        | _ -> None
    | If (c, tr, fl) ->
        match eval tenv c with
        | Some (VBool v) ->
            if v 
            then eval tenv tr
            else eval tenv fl 
        | _ -> None

// Test quick
open Combinator
open Parse

let mutable termEnv : TermEnv = Map.empty
let mutable typeEnv : TypeEnv = Map.empty

while true do
    printf "> "
    let input = System.Console.ReadLine()
    let ast = parseRepl input
    match ast with
    | Success (name, expr) -> 
        let typed, i = inferExpr typeEnv expr 0
        match typed with
        | Ok (_, ty) ->
            let res = eval termEnv expr
            if name <> "" then
                typeEnv <- extend typeEnv name ([name], ty)
            match res with
            | Some res -> 
                if name <> "" then
                    termEnv <- extend termEnv name res
                printfn "Result: %s" (prettyValue res)
            | None -> ()
            printfn "Type: %s" (ty |> renameFresh |> prettyType)
        | Error err -> printfn "Typing error: %A" err
    | _ -> printfn "Parsing error"