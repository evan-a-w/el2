open! Core
open! Shared

type t =
  | Unification_error of Ty.mono * Ty.mono
  | Occurs_check of Lowercase.t * Ty.mono
[@@deriving sexp]

exception Type_check of t
[@@deriving sexp]

let fail t = raise (Type_check t)
