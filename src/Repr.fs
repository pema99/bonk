module Repr

// AST and types
type Lit =
    | LFloat of float
    | LString of string
    | LInt of int
    | LBool of bool

type BinOp =
    | Plus
    | Minus
    | Star
    | Slash
    | Equal
    | NotEq
    | GreaterEq
    | LessEq
    | Greater
    | Less
    | And
    | Or

type Expr =
    | Var of string
    | App of Expr * Expr
    | Lam of string * Expr
    | Let of string * Expr * Expr
    | Lit of Lit
    | If of Expr * Expr * Expr
    | Op of Expr * BinOp * Expr
    | Tup of Expr list
    | Rec of Expr

type Kind =
    | Product of int
    | Constant of string 
    // TODO: Sum types

type Type =
    | TVar of string
    | TCon of string
    | TArr of Type * Type
    | TCtor of Kind * Type list

let tInt = TCon "int"
let tBool = TCon "bool"
let tFloat = TCon "float"
let tString = TCon "string"
let tVoid = TCon "void"