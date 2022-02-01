module Repr

// AST and types
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

type Pat =
    | PName of string
    | PTuple of string list
    // TODO: Sum types
    // TODO: Nested tuple patterns

type Lit =
    | LFloat of float
    | LString of string
    | LInt of int
    | LBool of bool

and Expr =
    | Var of string
    | App of Expr * Expr
    | Lam of Pat * Expr
    | Let of Pat * Expr * Expr
    | Lit of Lit
    | If of Expr * Expr * Expr
    | Op of Expr * BinOp * Expr
    | Tup of Expr list
    | Rec of Expr

type Kind =
    | KProduct of int
    | KConstant of string 
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