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

let rec mapM (f: 'a -> StateM<'s, 'b>) (t: 'a list) : StateM<'s, 'b list> = state {
    match t with
    | h :: t ->
        let! v = f h
        let! next = mapM f t
        return v :: next
    | _ -> return []
}
let rec foldM (f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        return! foldM f v t
    | _ -> return acc
}
let rec scanM (f: 'a -> 'b -> StateM<'s, 'a>) (acc: 'a) (t: 'b list) : StateM<'s, 'a list> = state {
    match t with
    | h :: t ->
        let! v = f acc h 
        let! next = scanM f v t
        return v :: next 
    | _ -> return []
}