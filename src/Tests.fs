module Tests

open Repr
open Inference
open Pretty
(*
// Tests
let checkTest i e a =
    match a with
    | Error err -> printfn "[%A] Error: %A" i err
    | Ok v ->
        if e = v then
            printfn "[%A] Pass." i
        else
            printfn "[%A] Fail:" i
            printfn "\tExpected: %A" e
            printfn "\tActual: %A" v

let cases = [
    tInt,                                               ELit (LInt 5)
    tBool,                                              ELit (LBool false)
    tInt,                                               EOp (ELit (LInt 5), Plus, ELit (LInt 6))
    tInt,                                               ELet (PName "c", ELit (LInt 5), EOp (EVar "c", Star, EVar "c"))
    TArrow (TVar "a", TArrow (TVar "a", TVar "a")),         ELet (PName "add", ELam (PName "a", ELam (PName "b", EOp (EVar "a", Slash, EVar "b"))), EVar ("add"))
    TArrow (TConst "bool", TArrow (TConst "int", TConst "int")),  ELam (PName "a", ELam(PName "b", EIf (EVar "a", ELit (LInt 5), EVar "b")))
    ]

let runTests() =
    printfn "Running tests..."
    cases
    |> List.iteri (fun i (t, e) -> checkTest i t (inferProgram e))

let prog1 = 
    EUnion ("Option", ["a"], [("None", tUnit); ("Some", TVar "a")],
        EApp (EVar "Some", ELit (LInt 3)))

let prog2 =
    EUnion ("List", ["a"],
            [("Cons", TCtor (KProduct, [TVar "a"; TCtor (KSum "List", [TVar "a"])]));
            ("Nil", tUnit)],
            EVar "Cons")

let prog3 =
    EUnion ("List", ["a"],
            [("Cons", TCtor (KProduct, [TVar "a"; TCtor (KSum "List", [TVar "a"])]));
            ("Nil", tUnit)],
            EVar "Nil")

printfn "%A" (inferProgram prog1 |> Result.map prettyType)
printfn "Cons :: %A" (inferProgram prog2 |> Result.map prettyType)
printfn "Nil :: %A" (inferProgram prog3 |> Result.map prettyType)

(*let prog1 = 
    Sum ("Option", ["a"], [("None", tUnit); ("Some", TVar "a")],
        Let (PUnion ("Some", "x"), App (Var "Some", Lit (LBool true)), Var "x")
    )
let prog1 = 
    Sum ("Option", ["a"], [("None", tUnit); ("Some", TVar "a")],
        Lam (PName "x", Let (PUnion ("Some", "y"), Var "x", Lit (LInt 3)))
    ) 
let prog1 = 
    Sum ("Option", ["a"], [("None", tUnit); ("Some", TVar "a")],
        Lam (PUnion ("Some", "x"), Var "x")
    )

printfn "%A" (inferProgram prog1 |> Result.map prettyType)*)
*)