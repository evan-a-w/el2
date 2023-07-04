open! Core

type ('go, 'stop) result = Go of 'go | Stop of 'stop [@@deriving sexp]

type ('go, 'stop, 'state) t = 'state -> ('go, 'stop) result * 'state
[@@deriving sexp]

let return x : (_, _, _) t = fun state -> (Go x, state)
let stop stop state = (Stop stop, state)
let run (t : (_, _, _) t) ~state = t state
let get state = (Go state, state)
let put state _ = (Go (), state)

let bind x ~f state =
  match x state with
  | Go x, state' -> f x state'
  | Stop stop, _ -> (Stop stop, state)

include Monad.Make3 (struct
  type nonrec ('go, 'stop, 'state) t = ('go, 'stop, 'state) t

  let return = return
  let bind = bind
  let map = `Define_using_bind
end)
