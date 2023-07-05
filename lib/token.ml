open! Core

type t =
  | Int of int
  | Float of float
  | Bool of bool
  | String of string
  | Arrow
  | Pipe
  | Comma
  | LParen
  | RParen
  | Symbol of string
[@@deriving sexp, compare, variants]
