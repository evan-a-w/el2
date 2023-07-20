open! Core
open! Infer
open! Shared
open! Frontend
open! State.Result.Let_syntax

let state_with_some_stuff =
  let open State.Let_syntax in
  let m =
    let%bind () = State.put empty_state in
    let%bind () =
      add_type "int" (Abstract (Unqualified "int", None))
      >>| Result.map_error ~f:Sexp.to_string_hum
      >>| Result.ok_or_failwith
    in
    let arg = Single_arg (Variance.Covariant, "a") in
    let mono = Abstract (Unqualified "list", None) in
    add_type_constructor arg "list" mono
  in
  State.run m ~state:empty_state |> snd

let%expect_test "type_expr single lit" =
  let lit = Ast.(Type_expr.Single Qualified.(Unqualified "int")) in
  let res, state =
    State.Result.run (type_of_type_expr lit) ~state:state_with_some_stuff
  in
  print_s [%message (res : (mono, Sexp.t) Result.t) (state : state)];
  [%expect
    {|
    ((res (Ok (Abstract (Unqualified int) ())))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list (Abstract (Unqualified list) ())))))
         (toplevel_types ((int (Abstract (Unqualified int) ()))))
         (toplevel_modules ()) (opened_modules ())))
       (current_qualification ()) (symbol_n 0)))) |}]

let%expect_test "type_expr multi lit" =
  let lit =
    Ast.(
      Type_expr.Multi
        ( Ast.Type_expr.Single (Qualified.Unqualified "int"),
          Qualified.Unqualified "list" ))
  in
  let res, state =
    State.Result.run (type_of_type_expr lit) ~state:state_with_some_stuff
  in
  print_s [%message (res : (mono, Sexp.t) Result.t) (state : state)];
  [%expect
    {|
    ((res (Ok (Abstract (Unqualified list) ((Abstract (Unqualified int) ())))))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list (Abstract (Unqualified list) ())))))
         (toplevel_types ((int (Abstract (Unqualified int) ()))))
         (toplevel_modules ()) (opened_modules ())))
       (current_qualification ()) (symbol_n 0)))) |}]

let%expect_test "type_expr multi lit" =
  let action : unit state_result_m =
    let%bind type_name, type_def, ast_tags =
      Parser.try_parse (Parser.typedef_p ())
        {| type a list = Cons (a, a list) | Nil |}
      |> State.return
    in
    let%bind () = process_type_def { type_name; type_def; ast_tags } in
    let%bind type_expr =
      Parser.try_parse (Parser.type_expr_p ()) {| int list |} |> State.return
    in
    let%map mono = type_of_type_expr type_expr in
    print_s [%message (mono : mono)]
  in
  (match State.Result.run action ~state:empty_state |> fst with
  | Ok () -> ()
  | Error error -> print_s [%message (error : Sexp.t)]);
  [%expect
    {| (mono (Enum ((Cons ((Tuple ((TyVar int) Recursive_constructor)))) (Nil ())))) |}]
