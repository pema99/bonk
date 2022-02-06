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
    | EVar of string
    | EApp of Expr * Expr
    | ELam of Pat * Expr
    | ELet of Pat * Expr * Expr
    | ELit of Lit
    | EIf of Expr * Expr * Expr
    | EOp of Expr * BinOp * Expr
    | ETuple of Expr list
    | EUnion of string * string list * (string * Type) list * Expr
    | EMatch of Expr * (Pat * Expr) list
    | ERec of Expr

and Kind =
    | KSum of string
    | KProduct of int
    | KConst of string 

and Type =
    | TVar of string
    | TConst of string
    | TArrow of Type * Type
    | TCtor of Kind * Type list

let tInt = TConst "int"
let tBool = TConst "bool"
let tFloat = TConst "float"
let tString = TConst "string"
let tVoid = TConst "void"
let tUnit = TConst "unit"
let sInt = ([], tInt)
let sBool = ([], tBool)
let sFloat = ([], tFloat)
let sString = ([], TConst "string")
let sVoid = ([], TConst "void")
let sUnit = ([], TConst "unit")