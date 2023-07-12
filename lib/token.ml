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
  | LBrack
  | RBrack
  | LBrace
  | RBrace
  | Colon
  | At
  | Semicolon
  | Dot
  | Symbol of string
  | Keyword of string
[@@deriving sexp, compare, variants, equal, hash]
