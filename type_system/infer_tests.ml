open! Core
open! Infer
open! Shared
open! Frontend
open! State.Result.Let_syntax

let state_with_some_stuff =
  let m =
    let%bind.State () = State.put empty_state in
    let%bind.State () = add_type "int" (Abstract (Unqualified "int", None)) in
    let arg = Single_arg (Variance.Covariant, "a") in
    let mono = Abstract (Unqualified "list", Some arg) in
    add_type_constructor arg "list" mono
  in
  State.run m ~state:empty_state |> snd

let%expect_test "type_expr single lit" =
  let lit = Ast.(Type_expr.Single Qualified.(Unqualified "int")) in
  let res, state =
    State.Result.run
      (process_type_def_lit_type_expr lit)
      ~state:state_with_some_stuff
  in
  print_s [%message (res : (mono, Sexp.t) Result.t) (state : state)];
  [%expect
    {|
    ((res (Ok (Abstract ())))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ())
         (toplevel_types
          ((int (Abstract ()))
           (list ((Type_function a0 Abstract) ((a0 Covariant))))))
         (toplevel_modules ()) (opened_modules ())))
       (current_qualification ()) (type_var_map ((a (a0)))) (symbol_n 0)))) |}]

let%expect_test "type_expr multi lit" =
  let lit =
    Ast.(
      Type_expr.Multi
        ( Ast.Single_or_tuple.Single
            (Ast.Type_expr.Single (Qualified.Unqualified "int")),
          Ast.Type_expr.Single (Qualified.Unqualified "list") ))
  in
  let res, state =
    State.Result.run
      (process_type_def_lit_type_expr lit)
      ~state:state_with_some_stuff
  in
  print_s [%message (res : (mono, Sexp.t) Result.t) (state : state)]
