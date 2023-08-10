open! Core
open! Shared
open! Frontend

module Literal = struct
  type t = Ast.Literal.t =
    | Unit
    | Int of int
    | Bool of bool
    | Float of float
    | String of string
    | Char of char
  [@@deriving sexp, equal, hash, compare]

  let type_proof_of_t = function
    | Unit -> Ty.unit_type
    | Int _ -> Ty.int_type
    | Bool _ -> Ty.bool_type
    | Float _ -> Ty.float_type
    | String _ -> Ty.string_type
    | Char _ -> Ty.char_type

  let mono_of_t x =
    let type_proof = type_proof_of_t x in
    Ty.Named type_proof

  let poly_of_t x =
    let mono = mono_of_t x in
    Ty.Mono mono
end

type node =
  | Var of Lowercase.t Qualified.t
  | Literal of Literal.t
  | Tuple of expr list Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and binding = binding_inner * Ty.poly [@@deriving sexp, equal, hash, compare]

and binding_inner =
  | Name_binding of Lowercase.t
  | Constructor_binding of Uppercase.t Qualified.t * binding option
  | Literal_binding of Literal.t
  | Record_binding of binding Lowercase.Map.t Qualified.t
  | Tuple_binding of binding list Qualified.t
  | Renamed_binding of binding * Lowercase.t
  | Reference_binding of binding
[@@deriving sexp, equal, hash, compare]

and let_each = binding * expr [@@deriving sexp, equal, hash, compare]

and let_def = Rec of let_each list | Nonrec of let_each
[@@deriving sexp, equal, hash, compare]

and expr = expr_inner * Ty.mono [@@deriving sexp, equal, hash, compare]

and expr_inner =
  | Node of node
  | If of expr * expr * expr
  | Lambda of binding * expr
  | App of expr * expr
  | Let_in of let_def * expr
  | Ref of expr
  | Deref of expr
  | Field_access of expr * Lowercase.t Qualified.t
  | Field_set of (expr * Lowercase.t Qualified.t * expr)
  | Match of expr * (binding * expr) list
[@@deriving sexp, equal, hash, compare]

let expr_of_literal x = (Node (Literal x), Literal.mono_of_t x)
