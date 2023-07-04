open! Core

type ('go, 'state, 'stop) t = Go of ('state -> 'go * 'state) | Stop of 'stop

let return x = Go (fun state -> (x, state))
let stop stop = Stop stop
let run_state (Go f) state = f state
let get = Go (fun state -> (state, state))
let put state = Go (fun _ -> ((), state))

let bind (type go state stop) (x : go) ~(f : go -> (go -> state -> (go * state)) =
  match x with
  | Go g ->
      fun state ->
        let x, state = g state in
        f x state
  | _ -> x
