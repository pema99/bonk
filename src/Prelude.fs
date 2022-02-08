module Prelude

open Repr

// Built in operators
let opSchemes: Map<BinOp, (string list * Type)> = Map.ofList [
    Plus, (["a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a")))
    Minus, (["a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a")))
    Star, (["a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a")))
    Slash, (["a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a")))
    Equal, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    NotEq, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    GreaterEq, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    LessEq, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    Greater, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    Less, (["a"], TArrow (TVar "a", TArrow (TVar "a", tBool)))
    And, ([], TArrow (tBool, TArrow (tBool, tBool)))
    Or, ([], TArrow (tBool, TArrow (tBool, tBool)))
    ]

// Instrinsics
let lengthString v =
    match v with
    | [VString v] -> Some (VInt (v.Length))
    | _ -> None

let indexString v =
    match v with
    | [VString v; VInt i] -> Some (VChar (v.[i]))
    | _ -> None

let substring v =
    match v with
    | [VString v; VInt f; VInt t] -> Some (VString (v.Substring(f, t)))
    | _ -> None

let funSchemes: Map<string, (string list * Type)> = Map.ofList [
    "lengthString", ([], TArrow (tString, tInt))
    "indexString", ([], TArrow (tInt, TArrow (tString, tChar)))
    "substring", ([], TArrow (tInt, TArrow (tInt, TArrow (tString, tString))))
]

let funShims: Map<string, Value> = Map.ofList [
    "lengthString", VIntrinsic ("lengthString", [])
    "indexString", VIntrinsic ("indexString", [])
    "substring", VIntrinsic ("substring", [])
]

// Name, (impl, arity)
let funImpls = Map.ofList [
    "lengthString", (lengthString, 1)
    "indexString",  (indexString,  2)
    "substring",    (substring,    3)
]