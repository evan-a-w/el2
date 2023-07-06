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
  | Colon
  | Symbol of string
  | Keyword of string
[@@deriving sexp, compare, variants]
