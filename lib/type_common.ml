open! Core
open Ast

type expanded_expr =
  [ `Unit
  | `Null
  | `Int of int
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of string
  | `Var of name path
  | `Tuple of expanded_expr list
  | `Array_lit of expanded_expr list
  | `Enum of upper_name path
  | `Struct of name path * (string * expanded_expr option) list
  | `Apply of expanded_expr * expanded_expr
  | `Inf_op of inf_op * expanded_expr * expanded_expr
  | `Pref_op of pref_op * expanded_expr
  | `Deref of expanded_expr (* prefix * *)
  | `Ref of expanded_expr (* prefix & *)
  | `Tuple_access of expanded_expr * int (* postfix . *)
  | `Field_access of expanded_expr * string path (* postfix . *)
  | `Index of expanded_expr * expanded_expr (* postfix [] *)
  | `If of expanded_expr * expanded_expr * expanded_expr
  | `Match of expanded_expr * (pattern * expanded_expr) list
  | `Let of string * expanded_expr * expanded_expr
  | `Assign of expanded_expr * expanded_expr
  | `Compound of expanded_expr
  | `Size_of of [ `Type of type_expr | `Expr of expanded_expr ]
  | `Assert of expanded_expr
  | `Return of expanded_expr
  | `Typed of expanded_expr * type_expr
  | `Assert_struct of string path * expanded_expr
  | `Assert_empty_enum_field of string path * expanded_expr
  | `Access_enum_field of string path * expanded_expr
  | `Unsafe_cast of expanded_expr
  | `Loop of expanded_expr
  | `Break of expanded_expr
  ]
[@@deriving sexp, compare]
