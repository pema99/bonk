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
    | PTuple of Pat list
    | PUnion of string * Pat
    | PConstant of Lit

and Lit =
    | LFloat of float
    | LString of string
    | LInt of int
    | LBool of bool
    | LUnit

and Expr =
    | Var of string
    | App of Expr * Expr
    | Lam of Pat * Expr
    | Let of Pat * Expr * Expr
    | Lit of Lit
    | If of Expr * Expr * Expr
    | Op of Expr * BinOp * Expr
    | Tup of Expr list
    | Sum of string * string list * (string * Type) list * Expr
    | Match of Expr * (Pat * Expr) list
    | Rec of Expr

and Kind =
    | KSum of string
    | KProduct of int
    | KConstant of string 
    // TODO: Sum types

and Type =
    | TVar of string
    | TCon of string
    | TArr of Type * Type
    | TCtor of Kind * Type list

let tInt = TCon "int"
let tBool = TCon "bool"
let tFloat = TCon "float"
let tString = TCon "string"
let tVoid = TCon "void"
let tUnit = TCon "unit"
let sInt = ([], tInt)
let sBool = ([], tBool)
let sFloat = ([], tFloat)
let sString = ([], TCon "string")
let sVoid = ([], TCon "void")
let sUnit = ([], TCon "unit")