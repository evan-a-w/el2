open! Core
open! Shared
open! Type_system
open! State.Result.Let_syntax

type state = unit [@@deriving sexp, equal, compare]

(* we take the set in stone inference_state from Type_system *)
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let rec transform_inner
  ~(state : Inference_state.state)
  (expr_inner : Typed_ast.expr_inner)
  : Ir.expr_inner state_result_m
  =
  match expr_inner with
  | Typed_ast.Node n -> transform_node ~state n
  | Typed_ast.If (a, b, c) ->
    let%bind a = transform_expr ~state a in
    let%bind b = transform_expr ~state b in
    let%map c = transform_expr ~state c in
    Ir.If (a, b, c)
  | Typed_ast.Lambda (b, e) ->
    let%bind e = transform_expr ~state e in
    let%map b = transform_binding ~state b in
    Ir.Lambda (b, e)
  | Typed_ast.App (a, b) ->
    let%bind a = transform_expr ~state a in
    let%map b = transform_expr ~state b in
    Ir.App (a, b)
  | Typed_ast.Let_in (let_def, e) ->
    let%bind let_def = transform_let_def ~state let_def in
    let%map e = transform_expr ~state e in
    Ir.Let_in (let_def, e)
  | Typed_ast.Ref e ->
    let%map e = transform_expr ~state e in
    Ir.Ref e
  | Typed_ast.Deref e ->
    let%map e = transform_expr ~state e in
    Ir.Deref e
  | Typed_ast.Field_access (e, s) ->
    let%map e = transform_expr ~state e in
    Ir.Field_access (e, s)
  | Typed_ast.Field_set (a, s, b) ->
    let%bind a = transform_expr ~state a in
    let%map b = transform_expr ~state b in
    Ir.Field_set (a, s, b)
  | Typed_ast.Match (e, cases) -> transform_cases ~state e cases

and transform_node ~state:_ _node = failwith "TODO"

and transform_binding ~state:_ binding rhs =
  let inner acc binding =
    match binding with
    | Typed_ast.Name_binding (s, id) -> (s, id), acc, rhs
    | Typed_ast.Constructor_binding (cons, rest) -> failwith "TODO"
    | Typed_ast.Literal_binding _
    | Typed_ast.Record_binding _
    | Typed_ast.Tuple_binding _
    | Typed_ast.Renamed_binding (_, _, _)
    | Typed_ast.Reference_binding _ -> failwith "TODO"
  in
  inner [] binding

and transform_let_def ~state:_ _let_def = failwith "TODO"
and transform_cases ~state:_ _e _cases = failwith "TODO"

and transform_expr ~state (expr_inner, mono) : Ir.expr state_result_m =
  let%map expr_inner = transform_inner ~state expr_inner in
  expr_inner, mono
;;
