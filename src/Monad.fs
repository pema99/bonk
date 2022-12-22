module Monad

type StateM<'s, 't> = 's -> Result<'t, string> * 's

type StateBuilder() =
    member inline this.Return (v: 't) : StateM<'s, 't> =
        fun s -> Ok v, s
    member inline this.ReturnFrom ([<InlineIfLambda>] m: StateM<'s, 't>) : StateM<'s, 't> =
        m
    member inline this.Zero () : StateM<'s, unit> =
        this.Return ()
    member inline this.Bind ([<InlineIfLambda>] m: StateM<'s, 't>, [<InlineIfLambda>] f: 't -> StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m s
            match a with
            | Ok v -> (f v) n
            | Error err -> Error err, n
    member inline this.Combine ([<InlineIfLambda>] m1: StateM<'s, 't>, [<InlineIfLambda>] m2: StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m1 s
            match a with
            | Ok _ -> m2 n
            | Error err -> Error err, n
    member inline this.Delay ([<InlineIfLambda>] f: unit -> StateM<'s, 't>) : StateM<'s, 't> =
        this.Bind (this.Return (), f)
    member this.While (f: unit -> bool, m : StateM<'s, unit>) : StateM<'s, unit> =
        fun s -> 
            if f() then 
                let a, n = m s
                match a with
                | Ok _ -> this.While(f, m) n
                | Error err -> (Error err, n)
            else (Ok (), s)
        
let state = StateBuilder()
let just = state.Return
let inline failure err = fun s -> Error err, s
let inline set v : StateM<'a, unit> = fun _ -> (Ok (), v)
let get : StateM<'a, 'a> = fun s -> (Ok s, s)
let inline fmap ([<InlineIfLambda>] f) ([<InlineIfLambda>] m) =
    fun s ->
        let a, n = m s
        match a with
        | Ok v -> Ok (f v), n
        | Error err -> Error err, n

let inline ( >>= ) ([<InlineIfLambda>] a) ([<InlineIfLambda>] b) = state.Bind(a, b)
let inline ( >>. ) ([<InlineIfLambda>] a) ([<InlineIfLambda>] b) = state.Combine(a, b)
let inline ( >=> ) ([<InlineIfLambda>] l: 'a -> StateM<'s, 'b>) ([<InlineIfLambda>] r: 'b -> StateM<'s, 'c>) (v: 'a) : StateM<'s, 'c> = state {
    let! lv = l v
    let! rv = r lv
    return rv
}

type ReaderStateM<'r, 's, 't> = StateM<'r * 's, 't>
let ask : ReaderStateM<'r, 's, 'r> =
    fun s ->
        let a, n = get s
        match a with
        | Ok v -> Ok (fst v), n
        | Error err -> Error err, n
let inline local ([<InlineIfLambda>] f: 'r -> 'r) ([<InlineIfLambda>] m: ReaderStateM<'r, 's, 't>) : ReaderStateM<'r, 's, 't> =
    fun s ->
        let res, o = get s
        match res with
        | Ok (r, s) ->
            let a, (_, n) = m (f r, s)
            match a with
            | Ok v -> Ok v, (r, n)
            | Error err -> Error err, (r, n)
        | Error err -> Error err, o


let rec inline mapM ([<InlineIfLambda>] f: 'a -> StateM<'s, 'b>) (t: 'a list) : StateM<'s, 'b list> =
    let rec inner t acc = state {
        match t with
        | h :: t ->
            let! v = f h
            return! inner t (v :: acc)
        | _ -> return List.rev acc
    }
    inner t List.empty
let inline mapM_ ([<InlineIfLambda>] f) t = mapM f t >>. just ()

let rec foldM (f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let inline foldM_ ([<InlineIfLambda>] f) acc t = foldM f acc t >>. just ()

let rec inline scanM ([<InlineIfLambda>] f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a list> =
    let rec inner va t acc = state {
        match t with
        | h :: t ->
            let! v = f va h
            return! inner v t (v :: acc)
        | _ -> return List.rev acc
    }
    inner acc t List.empty
let inline scanM_ ([<InlineIfLambda>] f) acc t = scanM f acc t >>. just ()