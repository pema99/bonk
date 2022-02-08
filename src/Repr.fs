module Repr

// AST and types
type BinOp =
    | Plus
    | Minus
    | Star
    | Slash
    | Modulo
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
    | LChar of char
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
    | EClass of string * (string * Type) list * Expr // name, (fname, ftype) // TODO: Bounds
    | EMember of Type * string  * (string * Expr) list * Expr// mtype, name, impls // TODO: Blanket impls
    | ERec of Expr

and Kind =
    | KSum of string
    | KProduct

and Type =
    | TVar of string
    | TConst of string
    | TArrow of Type * Type
    | TCtor of Kind * Type list
    | TBounded of string list * Type

let tInt = TConst "int"
let tBool = TConst "bool"
let tFloat = TConst "float"
let tString = TConst "string"
let tChar = TConst "char"
let tVoid = TConst "void"
let tUnit = TConst "unit"

// Just for REPL
type Decl =
    | DExpr of Expr
    | DLet of Pat * Expr
    | DUnion of string * string list * (string * Type) list 

type Value =
    | VUnit
    | VInt of int
    | VBool of bool
    | VFloat of float
    | VString of string
    | VChar of char
    | VTuple of Value list
    | VUnionCase of string * Value
    | VUnionCtor of string
    | VClosure of Pat * Expr * TermEnv
    | VLazy of Value Lazy
    | VIntrinsic of string * Value list

and TermEnv = Map<string, Value>