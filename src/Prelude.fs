module Prelude

open Repr

// Built in operators
let opSchemes: Map<BinOp, Scheme> = Map.ofList [
    Plus,       (["a"], (set ["Num", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a"))))
    Minus,      (["a"], (set ["Num", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a"))))
    Star,       (["a"], (set ["Num", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a"))))
    Slash,      (["a"], (set ["Num", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a"))))
    Modulo,     (["a"], (set ["Num", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", TVar "a"))))
    Equal,      (["a"], (set ["Eq", TVar "a"],  TArrow (TVar "a", TArrow (TVar "a", tBool))))
    NotEq,      (["a"], (set ["Eq", TVar "a"],  TArrow (TVar "a", TArrow (TVar "a", tBool))))
    GreaterEq,  (["a"], (set ["Ord", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", tBool))))
    LessEq,     (["a"], (set ["Ord", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", tBool))))
    Greater,    (["a"], (set ["Ord", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", tBool))))
    Less,       (["a"], (set ["Ord", TVar "a"], TArrow (TVar "a", TArrow (TVar "a", tBool))))
    BoolAnd,    ([],    (set [], TArrow (tBool, TArrow (tBool, tBool))))
    BoolOr,     ([],    (set [], TArrow (tBool, TArrow (tBool, tBool))))
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

let print v =
    match v with
    | [VString v] ->
        System.Console.Write (System.Text.RegularExpressions.Regex.Unescape v)
        Some VUnit
    | _ -> None

let read v =
    match v with
    | [VUnit] -> Some (VString (System.Console.ReadLine()))
    | _ -> None

let readFile v =
    match v with
    | [VString v] -> Some (VString (System.IO.File.ReadAllText v))
    | _ -> None

let toFloat v =
    match v with
    | [VFloat v] -> Some (VFloat (float v))
    | [VString v] -> Some (VFloat (float v))
    | [VChar v] -> Some (VFloat (float v))
    | [VInt v] -> Some (VFloat (float v))
    | [a] -> Some (VFloat 0.0)
    | _ -> None

let toString v =
    match v with
    | [VFloat v] -> Some (VString (string v))
    | [VString v] -> Some (VString (string v))
    | [VBool v] -> Some (VString (string v))
    | [VChar v] -> Some (VString (string v))
    | [VInt v] -> Some (VString (string v))
    | [a] -> Some (VString "")
    | _ -> None

let toBool v =
    match v with
    | [VString "true"] -> Some (VBool true)
    | [VString "false"] -> Some (VBool false)
    | [VFloat v] -> Some (VBool (v <> 0.0))
    | [VBool v] -> Some (VBool v)
    | [VChar v] -> Some (VBool (v <> char 0))
    | [VInt v] -> Some (VBool (v <> 0))
    | [a] -> Some (VBool false)
    | _ -> None
    
let toChar v =
    match v with
    | [VFloat v] -> Some (VChar (char v))
    | [VString v] -> Some (VChar (char v))
    | [VChar v] -> Some (VChar (char v))
    | [VInt v] -> Some (VChar (char v))
    | [a] -> Some (VChar (char 0))
    | _ -> None

let toInt v =
    match v with
    | [VFloat v] -> Some (VInt (int v))
    | [VString v] -> Some (VInt (int v))
    | [VBool v] -> Some (VInt (if v then 1 else 0))
    | [VChar v] -> Some (VInt (int v))
    | [VInt v] -> Some (VInt (int v))
    | [a] -> Some (VInt 0)
    | _ -> None

let mathOp1 f v =
    match v with
    | [VFloat v] -> Some (VFloat (f v))
    | [VInt v] -> Some (VFloat (f (float v)))
    | _ -> None

let mathOp2 f v =
    match v with
    | [VFloat l; VFloat r] -> Some (VFloat (f l r))
    | [VInt l; VInt r] -> Some (VFloat (f (float l) (float r)))
    | _ -> None

// TODO: Safe wrappers
let funSchemes: Map<string, Scheme> = Map.ofList [
    "lengthString", ([],    (set [], TArrow (tString, tInt)))
    "indexString",  ([],    (set [], TArrow (tString, TArrow (tInt, tChar))))
    "substring",    ([],    (set [], TArrow (tString, TArrow (tInt, TArrow (tInt, tString)))))
    "print",        ([],    (set [], TArrow (tString, tUnit)))
    "read",         ([],    (set [], TArrow (tUnit, tString)))
    "readFile",     ([],    (set [], TArrow (tString, tString)))
    "toFloat",      (["a"], (set ["ToFloat", TVar "a"], TArrow (TVar "a", tFloat)) )
    "toString",     (["a"], (set ["ToString", TVar "a"], TArrow (TVar "a", tString)) )
    "toBool",       (["a"], (set ["ToBool", TVar "a"], TArrow (TVar "a", tBool)) )
    "toChar",       (["a"], (set ["ToChar", TVar "a"], TArrow (TVar "a", tChar)) )
    "toInt",        (["a"], (set ["ToInt", TVar "a"], TArrow (TVar "a", tInt)))
    "sqrt",         ([],    (set [], TArrow (tFloat, tFloat)))
    "sin",          ([],    (set [], TArrow (tFloat, tFloat)))
    "cos",          ([],    (set [], TArrow (tFloat, tFloat)))
    "tan",          ([],    (set [], TArrow (tFloat, tFloat)))
    "asin",         ([],    (set [], TArrow (tFloat, tFloat)))
    "acos",         ([],    (set [], TArrow (tFloat, tFloat)))
    "atan",         ([],    (set [], TArrow (tFloat, tFloat)))
    "atan2",        ([],    (set [], TArrow (tFloat, TArrow (tFloat, tFloat))))
    "exp",          ([],    (set [], TArrow (tFloat, tFloat)))
    "pow",          ([],    (set [], TArrow (tFloat, TArrow (tFloat, tFloat))))
    "ln",           ([],    (set [], TArrow (tFloat, tFloat)))
    "floor",        ([],    (set [], TArrow (tFloat, tFloat)))
    "ceil",         ([],    (set [], TArrow (tFloat, tFloat)))
]

// Name, (impl, arity)
let funImpls = Map.ofList [
    "lengthString", (lengthString,  1)
    "indexString",  (indexString,   2)
    "substring",    (substring,     3)
    "print",        (print,         1)
    "read",         (read,          1)
    "toFloat",      (toFloat,       1) 
    "toString",     (toString,      1) 
    "toBool",       (toBool,        1) 
    "toChar",       (toChar,        1)
    "toInt",        (toInt,         1)
    "sqrt",         (mathOp1 sqrt,  1)
    "sin",          (mathOp1 sin,   1)
    "cos",          (mathOp1 cos,   1)
    "tan",          (mathOp1 tan,   1)
    "asin",         (mathOp1 asin,  1)
    "acos",         (mathOp1 acos,  1)
    "atan",         (mathOp1 atan,  1)
    "atan2",        (mathOp2 atan2, 2)
    "exp",          (mathOp1 exp,   1)
    "pow",          (mathOp2 ( ** ),2)
    "ln",           (mathOp1 log,   1)
    "floor",        (mathOp1 floor, 1)
    "ceil",         (mathOp1 ceil,  1)
]

let classes: ClassEnv = Map.ofList [
    "Num", ([], [
        tInt
        tFloat
        tChar
        tString // TODO: This is wrong!!
    ])
    "Eq", ([], [
        tInt
        tBool
        tFloat
        tString
        tChar
        tUnit
    ])
    "Ord", (["Eq"], [
        tInt
        tFloat
        tChar
    ])
    "ToString", ([], [
        tInt
        tBool
        tFloat
        tChar
        tUnit
        tString
    ])
    "ToFloat", ([], [
        tInt
        tString
        tChar
    ])
    "ToBool", ([], [
        tString
    ])
    "ToChar", ([], [
        tInt
        tString
    ])
    "ToInt", ([], [
        tFloat
        tString
        tChar
    ])
]

let loadLibrarySource name =
    use res =
        System.Reflection.Assembly
            .GetExecutingAssembly()
            .GetManifestResourceStream(name)
    let out = Array.create (int res.Length) (byte 0)
    res.Read(out, 0, int res.Length) |> ignore
    System.Text.Encoding.Default.GetString(out)

// Attempt to load std lib
let stdLib = loadLibrarySource "bonk.lib.bonk.prelude.bonk"
let jsStdLib = loadLibrarySource "bonk.lib.bonk.prelude_js.bonk"
let jsInstrincs = loadLibrarySource "bonk.lib.js.intrinsics.js"
let jsBuiltins = loadLibrarySource "bonk.lib.bonk.builtins_js.bonk"

// Keep track of files
let builtinFiles = Map.ofList [
    "lib/bonk/prelude.bonk", stdLib
    "lib/bonk/prelude_js.bonk", jsStdLib
    "lib/js/intrinsics.js", jsInstrincs
    "lib/bonk/builtins_js.bonk", jsBuiltins
]