module Tests

open Repr
open Inference

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
    tInt,                                               Lit (LInt 5)
    tBool,                                              Lit (LBool false)
    tInt,                                               Op (Lit (LInt 5), Plus, Lit (LInt 6))
    tInt,                                               Let (PName "c", Lit (LInt 5), Op (Var "c", Star, Var "c"))
    TArr (TVar "a", TArr (TVar "a", TVar "a")),         Let (PName "add", Lam (PName "a", Lam (PName "b", Op (Var "a", Slash, Var "b"))), Var ("add"))
    TArr (TCon "bool", TArr (TCon "int", TCon "int")),  Lam (PName "a", Lam(PName "b", If (Var "a", Lit (LInt 5), Var "b")))
    ]

let runTests() =
    printfn "Running tests..."
    cases
    |> List.iteri (fun i (t, e) -> checkTest i t (inferProgram e))