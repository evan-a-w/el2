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
  | Semicolon
  | Backslash
  | Symbol of string
  | Keyword of string
  | Hash
[@@deriving sexp, compare, variants, equal, hash]

let at = Symbol "@"
let dollar = Symbol "$"
let dot = Symbol "."
