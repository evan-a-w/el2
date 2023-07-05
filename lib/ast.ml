open! Core

type node =
  | Let of string * t
  (* if none is thunk *)
  | Lambda of string option * t
  | App of t * t
  | Let_in of string * t * t
  | If of t * t * t
  | Var of string
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
[@@deriving sexp]

and tag = { typ : string } [@@deriving sexp]
and t = { tag : tag; node : node } [@@deriving sexp]
