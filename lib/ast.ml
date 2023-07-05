open! Core

type node =
  | Lambda of string * t
  | App of t * t
  | Let of string * t * t
  | If of t * t * t
  | Var of string
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Wrapped of t
[@@deriving sexp]

and t = { type_expr : Types.Type_expr.t option; [@sexp.option] node : node }
[@@deriving sexp]

let untyped node = { type_expr = None; node }
