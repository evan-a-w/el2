open! Core

type node =
  | Let of string * t
  (* if none is thunk *)
  | Lambda of string * t
  | App of t * t
  | Let_in of string * t * t
  | If of t * t * t
  | Var of string
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Wrapped of t
[@@deriving sexp]

and t = { type_expr : Types.Type_expr.t Option.t; node : node }
[@@deriving sexp]

let untyped node = { type_expr = None; node }

(* type t = *)
(*   | Let of string * t *)
(*   (\* if none is thunk *\) *)
(*   | Lambda of string option * t *)
(*   | App of t * t *)
(*   | Let_in of string * t * t *)
(*   | If of t * t * t *)
(*   | Var of string *)
(*   | Unit *)
(*   | Int of int *)
(*   | Bool of bool *)
(*   | Float of float *)
(*   | String of string *)
(* [@@deriving sexp] *)
