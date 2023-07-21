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
      add_type "int" (Abstract (Unqualified "int", Lowercase.Map.empty, 0))
      >>| Result.map_error ~f:Sexp.to_string_hum
      >>| Result.ok_or_failwith
    in
    let arg = Single_arg (Variance.Covariant, "a") in
    let mono =
      Abstract
        (Unqualified "list", Lowercase.Map.of_alist_exn [ ("a", TyVar "a") ], 0)
    in
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
    ((res (Ok (Abstract ((Unqualified int) () 0))))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list
             (Abstract ((Unqualified list) ((a (TyVar a))) 0))))))
         (toplevel_types ((int (Abstract ((Unqualified int) () 0)))))
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
    ((res
      (Ok
       (Abstract
        ((Unqualified list) ((a (Abstract ((Unqualified int) () 0)))) 0))))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list
             (Abstract ((Unqualified list) ((a (TyVar a))) 0))))))
         (toplevel_types ((int (Abstract ((Unqualified int) () 0)))))
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
    {|
      (mono
       (Enum ((Unqualified list) ((a (TyVar int))) 1)
        ((Cons
          ((Tuple
            ((TyVar int)
             (Recursive_constructor ((Unqualified list) ((a (TyVar int))) 0))))))
         (Nil ())))) |}]

let infer_type_of_expr ~programs ~print_state =
  let action program : unit state_result_m =
    let%bind type_name, type_def, ast_tags =
      Parser.try_parse (Parser.typedef_p ())
        {| type a list = Cons (a, a list) | Nil |}
      |> State.return
    in
    let%bind () = process_type_def { type_name; type_def; ast_tags } in
    let%bind expr = Parser.try_parse Parser.parse_one program |> State.return in
    let%bind mono = mono_of_expr expr in
    let%map mono = apply_substs mono in
    print_s [%message (mono : mono)]
  in
  List.iter programs ~f:(fun program ->
      match
        (print_state, State.Result.run (action program) ~state:empty_state)
      with
      | true, (Ok (), state) -> print_s [%message (state : state)]
      | true, (Error error, state) ->
          print_s [%message (error : Sexp.t) (state : state)]
      | false, (Ok (), _) -> ()
      | false, (Error error, _) -> print_s [%message (error : Sexp.t)])

let%expect_test "simple" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| Cons (1, Nil) |}; {| Cons |}; {| Nil |} ];
  [%expect
    {|
    (mono
     (Enum ((Unqualified list) ((a (TyVar a0))) 1)
      ((Cons
        ((Tuple
          ((TyVar a0)
           (Recursive_constructor ((Unqualified list) ((a (TyVar a0))) 0))))))
       (Nil ()))))
    (mono
     (Lambda
      (Tuple
       ((TyVar b0)
        (Recursive_constructor ((Unqualified list) ((a (TyVar b0))) 0))))
      (Enum ((Unqualified list) ((a (TyVar a0))) 1)
       ((Cons
         ((Tuple
           ((TyVar a0)
            (Recursive_constructor ((Unqualified list) ((a (TyVar a0))) 0))))))
        (Nil ())))))
    (mono
     (Enum ((Unqualified list) ((a (TyVar a0))) 1)
      ((Cons
        ((Tuple
          ((TyVar a0)
           (Recursive_constructor ((Unqualified list) ((a (TyVar a0))) 0))))))
       (Nil ())))) |}]

let%expect_test "if_expr" =
  infer_type_of_expr ~print_state:false ~programs:[ "if true then 1 else 0" ];
  [%expect {|
    (mono (Abstract ((Unqualified int) () 0))) |}];
  infer_type_of_expr ~print_state:false ~programs:[ "if 1 then 1 else 0" ];
  [%expect
    {|
    (error
     ("types failed to unify" (first (Unqualified int))
      (second (Unqualified bool)))) |}];
  infer_type_of_expr ~print_state:false
    ~programs:[ "if true then \"hi\" else 0" ];
  [%expect
    {|
    (error
     ("types failed to unify" (first (Unqualified string))
      (second (Unqualified int)))) |}];
  infer_type_of_expr ~print_state:false
    ~programs:[ "if true then Cons (1, Nil) else Cons (2, Nil)" ];
  [%expect
    {|
    (mono
     (Enum ((Unqualified list) ((a (TyVar a0))) 1)
      ((Cons
        ((Tuple
          ((TyVar a0)
           (Recursive_constructor ((Unqualified list) ((a (TyVar a0))) 0))))))
       (Nil ())))) |}]

let%expect_test "match_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| match Nil with | Nil -> 0 | Cons (x, _) -> x |};
        {| match Nil with | Nil -> "a" | Cons (x, _) -> x |};
        {| match Nil with | 0 -> 1 | Cons (x, _) -> x |};
        {| match Cons (1, Nil) with | Nil -> 0 | Cons (x, _) -> x |};
        {| match Cons (1, Nil) with | Nil -> "a" | Cons (x, _) -> x |};
      ];
  [%expect
    {|
    (mono (Abstract ((Unqualified int) () 0)))
    (mono (Abstract ((Unqualified string) () 0)))
    (error
     ("failed to unify types" (first (Abstract ((Unqualified int) () 0)))
      (second
       (Enum ((Unqualified list) ((a (TyVar a0))) 1)
        ((Cons
          ((Tuple
            ((TyVar a0)
             (Recursive_constructor ((Unqualified list) ((a (TyVar a0))) 0))))))
         (Nil ()))))))
    (mono (Abstract ((Unqualified int) () 0)))
    (mono (Abstract ((Unqualified string) () 0))) |}]

let%expect_test "lambda_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| (fun x -> 1) |}; {| (fun x -> 1) 1 |} ];
  [%expect
    {|
    (mono (Lambda (TyVar a0) (Abstract ((Unqualified int) () 0))))
    (mono (Abstract ((Unqualified int) () 0))) |}]

let%expect_test "let_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = (fun x -> 1) in x 1 |};
        {| let x = fun y -> y in x |};
        {| (fun x -> match x with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) |};
      ];
  [%expect
    {|
    (mono (Abstract ((Unqualified int) () 0)))
    (mono (Lambda (TyVar b0) (TyVar b0)))
    (mono (Lambda (TyVar a0) (Abstract ((Unqualified int) () 0)))) |}]

let%expect_test "let_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {|
        let x = (fun x -> match x with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) in
        let y = x 1 in
        y |};
      ];
  [%expect
    {|
    (mono (TyVar f0)) |}]
