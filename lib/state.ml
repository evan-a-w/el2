open! Core

type ('a, 'state) t = 'state -> 'a * 'state [@@deriving sexp]

let return x : ('a, _) t = fun state -> (x, state)
let run (t : (_, _) t) ~state = t state
let get state = (state, state)
let put state : (unit, 'state) t = fun _ -> ((), state)

let bind x ~f state =
  let x, state' = x state in
  f x state'

include Monad.Make2 (struct
  type nonrec ('a, 'state) t = ('a, 'state) t

  let return = return
  let bind = bind
  let map = `Define_using_bind
end)

module Result = struct
  type nonrec ('a, 'error, 'state) t = (('a, 'error) Result.t, 'state) t
  [@@deriving sexp]

  let return x : (_, _, _) t = fun state -> (Ok x, state)
  let error error state = (Error error, state)
  let run (t : (_, _, _) t) ~state = t state
  let get state = (Ok state, state)
  let put state _ = (Ok (), state)

  let map_error t ~f state =
    match t state with
    | Ok x, state' -> (Ok x, state')
    | Error e, state' -> (Error (f e), state')

  let first (type a error state) (xs : (a, error, state) t list) :
      (a, error list, state) t =
    let errors : error list ref = ref [] in
    let rec loop xs state =
      match xs with
      | [] -> (Error !errors, state)
      | x :: xs -> (
          let x, state' = x state in
          match x with
          | Ok _ as res -> (res, state')
          | Error e ->
              errors := e :: !errors;
              loop xs state)
    in
    fun state -> loop xs state

  let ( <|> ) a b state =
    match a state with Ok x, state' -> (Ok x, state') | Error _, _ -> b state

  let bind x ~f state =
    match x state with
    | Ok x, state' -> f x state'
    | (Error _ as e), _ -> (e, state)

  include Monad.Make3 (struct
    type nonrec ('go, 'stop, 'state) t = ('go, 'stop, 'state) t

    let return = return
    let bind = bind
    let map = `Define_using_bind
  end)
end