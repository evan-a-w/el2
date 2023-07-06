open! Core

type node =
  | Lambda of binding * t
  | App of t * t
  | Let of binding * t * t
  | If of t * t * t
  | Var of binding
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Wrapped of t
[@@deriving sexp]

and binding = (string * Types.Type_expr.t option[@sexp.option])
[@@deriving sexp]

and t = { type_expr : Types.Type_expr.t option; [@sexp.option] node : node }
[@@deriving sexp]

let untyped node = { type_expr = None; node }
