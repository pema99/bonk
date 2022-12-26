module Repr

// Spans
type Loc = (int * int)
type Span = (Loc * Loc)
type Spanned<'t> = ('t * Span)
let dummySpan = ((0, 0), (0, 0))

// Error info
type ErrorInfo = {
    span: Span
    msg: string
}
type FileErrorInfo = {
    file: string
    span: Span
    msg: string
}

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

type Qualifier =
    | QImpure
    | QMemoize

// Tokens
type Token =
    // Operators, literals, identifiers, types
    | Op of BinOp
    | Lit of Literal
    | Ident of string
    | TypeDesc of Type
    | Qual of Qualifier
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
    | ERaw   of QualType option * string

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
    | DClass  of string * string list * (string * Type) list // name, (fname, ftype)
    | DMember of Pred * (string * ExprRaw<'t>) list          // pred, impls

and DeclRaw<'t, 'u> = {
    kind: DeclKind<'t>
    span: Span
    qualifiers: Qualifier Set
    data: 'u
}

and UntypedExpr = ExprRaw<unit>
and UntypedDecl = DeclRaw<unit, unit>
and UntypedProgram = string * UntypedDecl list
and TypedExpr = ExprRaw<QualType>
and TypedDecl = DeclRaw<QualType, unit>
and TypedProgram = string * TypedDecl list

// Primitive types
and PrimType =
    | TInt
    | TBool
    | TFloat
    | TString
    | TChar
    | TVoid
    | TUnit
    | TOpaque

// Kinds of type constructors
and Kind =
    | KVar of string
    | KSum of string
    | KProduct
    | KArrow

// Concrete types
and Type =
    | TVar   of string
    | TConst of PrimType
    | TCtor  of Kind * Type list

// Type predicates, used to handle typeclasses
and Pred = (string * Type)              // ie. (Num 'a)
and Class = (string list * Type list)   // Requirements, Instances. ie. [Ord], [Things that implement Eq]
and QualType = (Pred Set * Type)

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
let tInt = TConst TInt
let tBool = TConst TBool
let tFloat = TConst TFloat
let tString = TConst TString
let tChar = TConst TChar
let tVoid = TConst TVoid
let tUnit = TConst TUnit
let tOpaque = TConst TOpaque

// Dummy values when we need to construct fake expressions
let dummyType = tVoid
let dummyQualType = (Set.empty, dummyType)

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