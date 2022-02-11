module Monad

type StateM<'s, 't> = 's -> Result<'t, string> * 's

type StateBuilder() =
    member this.Return (v: 't) : StateM<'s, 't> =
        fun s -> Ok v, s
    member this.ReturnFrom (m: StateM<'s, 't>) : StateM<'s, 't> =
        m
    member this.Zero () : StateM<'s, unit> =
        this.Return ()
    member this.Bind (m: StateM<'s, 't>, f: 't -> StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m s
            match a with
            | Ok v -> (f v) n
            | Error err -> Error err, n
    member this.Combine (m1: StateM<'s, 't>, m2: StateM<'s, 'u>) : StateM<'s, 'u> =
        fun s ->
            let a, n = m1 s
            match a with
            | Ok _ -> m2 n
            | Error err -> Error err, n
    member this.Delay (f: unit -> StateM<'s, 't>) : StateM<'s, 't> =
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
let failure err = fun s -> Error err, s
let set v : StateM<'a, unit> = fun _ -> (Ok (), v)
let get : StateM<'a, 'a> = fun s -> (Ok s, s)
let fmap f m =
    fun s ->
        let a, n = m s
        match a with
        | Ok v -> Ok (f v), n
        | Error err -> Error err, n

let ( >>= ) a b = state.Bind(a, b)
let ( >>. ) a b = state.Combine(a, b)
let ( >=> ) (l: 'a -> StateM<'s, 'b>) (r: 'b -> StateM<'s, 'c>) (v: 'a) : StateM<'s, 'c> = state {
    let! lv = l v
    let! rv = r lv
    return rv
}

type ReaderState<'r, 's, 't> = StateM<'r * 's, 't>
let ask : ReaderState<'r, 's, 'r> =
    fun s ->
        let a, n = get s
        match a with
        | Ok v -> Ok (fst v), n
        | Error err -> Error err, n
let local (f: 'r -> 'r) (m: ReaderState<'r, 's, 't>) : ReaderState<'r, 's, 't> =
    fun s ->
        let res, o = get s
        match res with
        | Ok (r, s) ->
            let a, n = m (f r, s)
            match a with
            | Ok v -> Ok v, n
            | Error err -> Error err, n
        | Error err -> Error err, o


let rec mapM (f: 'a -> StateM<'s, 'b>) (t: 'a list) : StateM<'s, 'b list> = state {
    match t with
    | h :: t ->
        let! v = f h
        let! next = mapM f t
        return v :: next
    | _ -> return []
}
let mapM_ f t = mapM f t >>. just ()

let rec foldM (f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let foldM_ f acc t = foldM f acc t >>. just ()

let rec scanM (f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a list> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        let! next = scanM f v t
        return v :: next 
    | _ -> return []
}
let scanM_ f acc t = scanM f acc t >>. just ()
