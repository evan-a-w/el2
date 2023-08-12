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

let pprint_t = function
  | Int i -> Int.to_string i |> PPrint.string
  | Float f -> Float.to_string f |> PPrint.string
  | Bool b -> Bool.to_string b |> PPrint.string
  | Char c -> "'" ^ Char.to_string c ^ "'" |> PPrint.string
  | String s -> "\"" ^ s ^ "\"" |> PPrint.string
  | Arrow -> "->" |> PPrint.string
  | Pipe -> "|" |> PPrint.string
  | Comma -> "," |> PPrint.string
  | LParen -> "(" |> PPrint.string
  | RParen -> ")" |> PPrint.string
  | LBrack -> "[" |> PPrint.string
  | RBrack -> "]" |> PPrint.string
  | LBrace -> "{" |> PPrint.string
  | RBrace -> "}" |> PPrint.string
  | Colon -> ":" |> PPrint.string
  | Semicolon -> ";" |> PPrint.string
  | Backslash -> "\\" |> PPrint.string
  | Symbol s -> s |> PPrint.string
  | Keyword s -> s |> PPrint.string
  | Hash -> "#" |> PPrint.string
;;
