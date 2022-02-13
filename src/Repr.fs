module Repr

// Binary operators
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

// Patterns
type Pat =
    | PName of string
    | PTuple of Pat list
    | PUnion of string * Pat
    | PConstant of Lit

// Literals
and Lit =
    | LFloat of float
    | LString of string
    | LInt of int
    | LBool of bool
    | LChar of char
    | LUnit

// Expression AST
and Expr =
    | EVar of string
    | EApp of Expr * Expr
    | ELam of Pat * Expr
    | ELet of Pat * Expr * Expr
    | ELit of Lit
    | EIf of Expr * Expr * Expr
    | EOp of Expr * BinOp * Expr
    | ETuple of Expr list
    | EMatch of Expr * (Pat * Expr) list
    | ERec of Expr

// Kinds of type constructors
and Kind =
    | KSum of string
    | KProduct
    | KConst of string 

// Concrete types
and Type =
    | TVar of string
    | TConst of string
    | TArrow of Type * Type
    | TCtor of Kind * Type list

// Type predicates, used to handle typeclasses
and Pred = (string * Type)              // ie. (Num 'a)
and Inst = Pred list * Pred             // ie. (Sub 'a, Zero 'a) |- (Num 'a), or |- (Num int)
and Class = (string list * Inst list)   // Requirements, Instances. ie. [Ord], [Things that implement Eq]
and QualType = (Pred list * Type)

// Type schemes for polytypes
type Scheme = string list * QualType

// Different kinds of environment
type ClassEnv = Map<string, Class> // name -> typeclass data
type ClassBinding = string * Class
type ImplBinding = string * Inst

type TypeEnv = Map<string, Scheme> // name -> scheme
type VarBinding = string * Scheme

type UserEnv = Map<string, int>    // name -> arity
type SumBinding = string * int

type EnvUpdate = VarBinding list * SumBinding list * ClassBinding list * ImplBinding list

// Primitive types
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
    | DClass of string * string list * (string * Type) list // name, reqs, (fname, ftype)
    | DMember of Pred list * Pred * (string * Expr) list    // blankets, pred, impls

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