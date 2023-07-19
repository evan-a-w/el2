open! Core

type t =
  | Int of int
  | Float of float
  | Bool of bool
  | Char of char
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
  | Backslash
  | Symbol of string
  | Keyword of string
[@@deriving sexp, compare, variants, equal, hash]
