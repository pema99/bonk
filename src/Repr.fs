module Repr

// Spans
type Loc = (int * int)
type Span = (Loc * Loc)
type Spanned<'t> = ('t * Span)
let dummySpan = ((0, 0), (0, 0))

// Literals
type Literal =
    | LFloat  of float
    | LString of string
    | LInt    of int
    | LBool   of bool
    | LChar   of char
    | LUnit

// Operators
type BinOp =
    | Plus | Minus | Star | Slash
    | Equal | NotEq
    | Greater | GreaterEq
    | Less | LessEq
    | BoolAnd | BoolOr
    | Modulo

// Tokens
type Token =
    // Operators, literals, identifiers, types
    | Op of BinOp
    | Lit of Literal
    | Ident of string
    | TypeDesc of Type
    | RawBlock of Spanned<Token> list * string
    // Keywords
    | Let | In
    | If | Then | Else
    | Sum | Match | With
    | Class | Of | Member
    | Rec | And | Import
    // Symbols
    | LParen | RParen
    | LBrack | RBrack
    | LBrace | RBrace
    | Comma | Pipe | Colon
    | Semicolon | Arrow | Tick
    | PipeLeft | PipeRight

// Patterns
and Pattern =
    | PName     of string
    | PTuple    of Pattern list
    | PUnion    of string * Pattern
    | PConstant of Literal

// Expression AST
and ExprKind<'t> =
    | EVar   of string
    | EApp   of ExprRaw<'t> * ExprRaw<'t>
    | ELam   of Pattern * ExprRaw<'t>
    | ELet   of Pattern * ExprRaw<'t> * ExprRaw<'t>
    | ELit   of Literal
    | EIf    of ExprRaw<'t> * ExprRaw<'t> * ExprRaw<'t>
    | EOp    of ExprRaw<'t> * BinOp * ExprRaw<'t>
    | ETuple of ExprRaw<'t> list
    | EMatch of ExprRaw<'t> * (Pattern * ExprRaw<'t>) list
    | EGroup of (string * ExprRaw<'t>) list * ExprRaw<'t>
    | ERaw   of Type option * string // TODO: This should be QualType, not Type

and ExprRaw<'t> = {
    kind: ExprKind<'t>
    span: Span
    data: 't
}

and DeclKind<'t> =
    | DExpr   of ExprRaw<'t>
    | DLet    of Pattern * ExprRaw<'t>
    | DGroup  of (string * ExprRaw<'t>) list
    | DUnion  of string * string list * (string * Type) list 
    | DClass  of string * string list * (string * Type) list // name, reqs, (fname, ftype)
    | DMember of Pred Set * Pred * (string * ExprRaw<'t>) list     // blankets, pred, impls

and DeclRaw<'t> = {
    akind: DeclKind<'t>
    aspan: Span
    adata: 't
}

and Expr = ExprRaw<unit>
and Decl = DeclRaw<unit>

// Kinds of type constructors
and Kind =
    | KSum   of string
    | KProduct

// Concrete types
// TODO: Unify these into a simpler repr
and Type =
    | TVar   of string
    | TConst of string
    | TArrow of Type * Type
    | TCtor  of Kind * Type list

// Type predicates, used to handle typeclasses
and Pred = (string * Type)              // ie. (Num 'a)
and Class = (string list * Type list)   // Requirements, Instances. ie. [Ord], [Things that implement Eq]
and QualType = (Pred Set * Type)

type TypedExpr =
    | TEVar   of QualType * string
    | TEApp   of QualType * TypedExpr * TypedExpr
    | TELam   of QualType * Pattern * TypedExpr
    | TELet   of QualType * Pattern * TypedExpr * TypedExpr
    | TELit   of QualType * Literal
    | TEIf    of QualType * TypedExpr * TypedExpr * TypedExpr
    | TEOp    of QualType * TypedExpr * BinOp * TypedExpr
    | TETuple of QualType * TypedExpr list
    | TEMatch of QualType * TypedExpr * (Pattern * TypedExpr) list
    | TEGroup of QualType * (string * TypedExpr) list * TypedExpr 
    | TERaw   of QualType * string

type TypedDecl =
    | TDExpr   of TypedExpr
    | TDLet    of Pattern * TypedExpr
    | TDGroup  of (string * TypedExpr) list
    | TDUnion  of string * string list * (string * Type) list 
    | TDClass  of string * string list * (string * Type) list  // name, reqs, (fname, ftype)
    | TDMember of Pred Set * Pred * (string * TypedExpr) list // blankets, pred, impls

// Type schemes for polytypes
type Scheme = string list * QualType

// Different kinds of environment
type ClassEnv = Map<string, Class> // name -> typeclass data
type ClassBinding = string * Class
type ImplBinding = string * Type

type TypeEnv = Map<string, Scheme> // name -> scheme
type VarBinding = string * Scheme

type UserEnv = Map<string, (string list * (string * Type) list)>    // name -> tvars, (string * type) list
type SumBinding = string * (string list * (string * Type) list)

type EnvUpdate = VarBinding list * SumBinding list * ClassBinding list * ImplBinding list

// Primitive types
let tInt = TConst "int"
let tBool = TConst "bool"
let tFloat = TConst "float"
let tString = TConst "string"
let tChar = TConst "char"
let tVoid = TConst "void"
let tUnit = TConst "unit"
let tOpaque = TConst "opaque"

// Just for REPL
type Value =
    | VUnit
    | VInt       of int
    | VBool      of bool
    | VFloat     of float
    | VString    of string
    | VChar      of char
    | VTuple     of Value list
    | VUnionCase of string * Value
    | VUnionCtor of string
    | VClosure   of string list * Pattern * TypedExpr * TermEnv
    | VIntrinsic of string * Value list
    | VOverload  of TypedExpr list * int * (TypedExpr) list

and TermEnv = Map<string, Value>