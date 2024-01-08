open! Core
open! Types
open! Typed_ast

let eval ~(state : Type_check.Type_state.t) ~(expr : Type_check.expr)
  : Type_check.expr
  =
  let _ = state, expr in
  failwith "TODO"
;;
