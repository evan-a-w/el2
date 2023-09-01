open! Core
open! Shared
open! Type_system
open! State.Result.Let_syntax

type state = unit [@@deriving sexp, equal, compare]

(* we take the set in stone inference_state from Type_system *)
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let transform_inner
  ~(state : Inference_state.state)
  (expr_inner : Typed_ast.expr_inner)
  : Ir.expr_inner state_result_m
  =
  let _ = state, expr_inner in
  failwith "TODO"
;;

let transform_expr ~state (expr_inner, mono) : Ir.expr state_result_m =
  let%map expr_inner = transform_inner ~state expr_inner in
  expr_inner, mono
;;
