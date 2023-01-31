module Monad

// Type shortcuts
[<Struct>]
type StateM<'s, 't, 'e> = State of ('s -> Result<'t, 'e> * 's)
type ResultM<'t, 'e> = StateM<unit, 't, 'e>
type ReaderStateM<'r, 's, 't, 'e> = StateM<'r * 's, 't, 'e>
type ReaderM<'r, 't, 'e> = ReaderStateM<'r, unit, 't, 'e>

let unstate (State m) = m

let runStateM (monad: StateM<'s, 't, 'e>) (state: 's) : Result<'t, 'e> * 's =
    unstate monad state

let runResultM (monad: ResultM<'t, 'e>) : Result<'t, 'e> =
    unstate monad () |> fst

let runReaderStateM (monad: ReaderStateM<'r, 's, 't, 'e>) (env: 'r) (state: 's) : Result<'t, 'e> * 's =
    let res, state = runStateM monad (env, state)
    res, snd state

let runReaderM (monad: ReaderM<'r, 't, 'e>) (env: 'r) : Result<'t, 'e> =
    let res, _ = runStateM monad (env, ())
    res

// Main CE builder
type StateBuilder() =
    member inline this.Return (v: 't) : StateM<'s, 't, 'e> =
        State (fun s -> Ok v, s)
    member inline this.ReturnFrom (m: StateM<'s, 't, 'e>) : StateM<'s, 't, 'e> =
        m
    member inline this.Zero () : StateM<'s, unit, 'e> =
        this.Return ()
    member inline this.Bind (m: StateM<'s, 't, 'e>, [<InlineIfLambda>] f: 't -> StateM<'s, 'u, 'e>) : StateM<'s, 'u, 'e> =
        State (fun s ->
            let a, n = unstate m s
            match a with
            | Ok v -> unstate (f v) n
            | Error err -> Error err, n)
    member inline this.Combine (m1: StateM<'s, 't, 'e>, m2: StateM<'s, 'u, 'e>) : StateM<'s, 'u, 'e> =
        State (fun s ->
            let a, n = unstate m1 s
            match a with
            | Ok _ -> unstate m2 n
            | Error err -> Error err, n)
    member inline this.Delay ([<InlineIfLambda>] f: unit -> StateM<'s, 't, 'e>) : StateM<'s, 't, 'e> =
        this.Bind (this.Return (), f)
    member this.While (f: unit -> bool, m : StateM<'s, unit, 'e>) : StateM<'s, unit, 'e> =
        State (fun s -> 
            if f() then 
                let a, n = unstate m s
                match a with
                | Ok _ -> unstate (this.While(f, m)) n
                | Error err -> (Error err, n)
            else (Ok (), s))

// General utilities
let state = StateBuilder()
let just = state.Return
let inline failure err = State (fun s -> Error err, s)
let inline set v : StateM<'a, unit, 'e> = State (fun _ -> (Ok (), v))
let inline setR v : ReaderStateM<'r, 's, unit, 'e> = State (fun (r, _) -> (Ok (), (r, v)))
let get : StateM<'a, 'a, 'e> = State (fun s -> (Ok s, s))
let getR : ReaderStateM<'r, 'a, 'a, 'e> = State (fun s -> (Ok (snd s), s))
let inline modify (f: 'a -> 'a) : StateM<'a, unit, 'e> = State (fun s -> (Ok (), f s))
let inline modifyR (f: 'a -> 'a) : ReaderStateM<'r, 'a, unit, 'e> = State (fun (r, s) -> (Ok (), (r, f s)))
let inline fmap ([<InlineIfLambda>] f: 't -> 'u) (m: StateM<'s, 't, 'e>): StateM<'s, 'u, 'e> =
    State (fun s ->
        let a, n = unstate m s
        match a with
        | Ok v -> Ok (f v), n
        | Error err -> Error err, n)
let inline fmapError ([<InlineIfLambda>] f: 'e -> 'f) (m: StateM<'s, 't, 'e>): StateM<'s, 't, 'f> =
    State (fun s ->
        let a, n = unstate m s
        match a with
        | Ok v -> Ok v, n
        | Error err -> Error (f err), n)

let inline ( >>= ) (a) (b) = state.Bind(a, b)
let inline ( >>. ) (a) (b) = state.Combine(a, b)
let inline ( >=> ) ([<InlineIfLambda>] l: 'a -> StateM<'s, 'b, 'e>) ([<InlineIfLambda>] r: 'b -> StateM<'s, 'c, 'e>) (v: 'a) : StateM<'s, 'c, 'e> = state {
    let! lv = l v
    let! rv = r lv
    return rv
}
let inline ( <!> ) a b = fmap a b
let inline ( =<< ) a b = b >>= a
let inline ( .<< ) a b = b >>. a
let inline ( <=< ) a b = b >=> a

let rec inline mapM ([<InlineIfLambda>] f: 'a -> StateM<'s, 'b, 'e>) (t: 'a list) : StateM<'s, 'b list, 'e> =
    let rec inner t acc = state {
        match t with
        | h :: t ->
            let! v = f h
            return! inner t (v :: acc)
        | _ -> return List.rev acc
    }
    inner t List.empty
let inline mapM_ ([<InlineIfLambda>] f) t = mapM f t >>. just ()

let rec foldM (f: 'a -> 'b -> StateM<'s, 'a, 'e>) (acc: 'a) (t: 'b list) : StateM<'s, 'a, 'e> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let inline foldM_ ([<InlineIfLambda>] f) acc t = foldM f acc t >>. just ()

let rec inline scanM ([<InlineIfLambda>] f: 'a -> 'b -> StateM<'s, 'a, 'e>) (acc: 'a) (t: 'b list) : StateM<'s, 'a list, 'e> =
    let rec inner va t acc = state {
        match t with
        | h :: t ->
            let! v = f va h
            return! inner v t (v :: acc)
        | _ -> return List.rev acc
    }
    inner acc t List.empty
let inline scanM_ ([<InlineIfLambda>] f) acc t = scanM f acc t >>. just ()

// Reader functionality
let ask : ReaderStateM<'r, 's, 'r, 'e> =
    State (fun s ->
        let a, n = unstate get s
        match a with
        | Ok v -> Ok (fst v), n
        | Error err -> Error err, n)
let inline local ([<InlineIfLambda>] f: 'r -> 'r) (m: ReaderStateM<'r, 's, 't, 'e>) : ReaderStateM<'r, 's, 't, 'e> =
    State (fun s ->
        let res, o = unstate get s
        match res with
        | Ok (r, s) ->
            let a, (_, n) = unstate m (f r, s)
            match a with
            | Ok v -> Ok v, (r, n)
            | Error err -> Error err, (r, n)
        | Error err -> Error err, o)