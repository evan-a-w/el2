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
        ((toplevel_vars
          ((& ((Forall a (Mono (Lambda (TyVar a) (Pointer (TyVar a)))))))))
         (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list
             (Abstract ((Unqualified list) ((a (TyVar a))) 0))))))
         (toplevel_types
          ((bool (Abstract ((Unqualified bool) () 0)))
           (char (Abstract ((Unqualified char) () 0)))
           (float (Abstract ((Unqualified float) () 0)))
           (int (Abstract ((Unqualified int) () 0)))
           (string (Abstract ((Unqualified string) () 0)))
           (unit (Abstract ((Unqualified unit) () 0)))))
         (toplevel_modules ()) (opened_modules ())))
       (current_qualification ()) (type_vars ()) (current_level 0) (symbol_n 0)))) |}]

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
        ((toplevel_vars
          ((& ((Forall a (Mono (Lambda (TyVar a) (Pointer (TyVar a)))))))))
         (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((list
            ((Single_arg Covariant a) list
             (Abstract ((Unqualified list) ((a (TyVar a))) 0))))))
         (toplevel_types
          ((bool (Abstract ((Unqualified bool) () 0)))
           (char (Abstract ((Unqualified char) () 0)))
           (float (Abstract ((Unqualified float) () 0)))
           (int (Abstract ((Unqualified int) () 0)))
           (string (Abstract ((Unqualified string) () 0)))
           (unit (Abstract ((Unqualified unit) () 0)))))
         (toplevel_modules ()) (opened_modules ())))
       (current_qualification ()) (type_vars ()) (current_level 0) (symbol_n 0)))) |}]

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
       (Enum ((Unqualified list) ((a (Abstract ((Unqualified int) () 0)))) 1)
        ((Cons
          ((Tuple
            ((Abstract ((Unqualified int) () 0))
             (Recursive_constructor
              ((Unqualified list) ((a (Abstract ((Unqualified int) () 0)))) 0))))))
         (Nil ())))) |}]

let define_types ~type_exprs =
  let action type_expr =
    let%bind type_name, type_def, ast_tags =
      Parser.try_parse (Parser.typedef_p ()) type_expr |> State.return
    in
    process_type_def { type_name; type_def; ast_tags }
  in
  State.Result.all_unit (List.map type_exprs ~f:action)

let type_exprs =
  [
    {| type a option = None | Some a |};
    {| type a node = { value : a; mutable next : &(a node) option } |};
    {| type a list = Cons (a, a list) | Nil |};
    {| type a ref_list = Ref_cons (&a, a ref_list) | Ref_nil |};
  ]

let infer_type_of_expr ~programs ~print_state =
  let action program : unit state_result_m =
    let%bind () = define_types ~type_exprs in
    let%bind expr = Parser.try_parse Parser.parse_one program |> State.return in
    (* let%bind expr = replace_user_ty_vars expr in *)
    (* print_s [%message (expr : Ast.expr)]; *)
    let%bind mono = mono_of_expr expr in
    let%map mono = apply_substs mono in
    let sexp = show_mono mono in
    print_s sexp
  in
  List.iter programs ~f:(fun program ->
      match
        (print_state, State.Result.run (action program) ~state:empty_state)
      with
      | true, (Ok (), state) ->
          let mono_ufds = show_mono_ufds state.mono_ufds in
          print_s [%message (mono_ufds : Sexp.t)]
      | true, (Error error, state) ->
          print_s [%message (error : Sexp.t) (state : state)]
      | false, (Ok (), _) -> ()
      | false, (Error error, _) -> print_s [%message (error : Sexp.t)])

let%expect_test "simple" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| Cons (1, Nil) |};
        {| Cons |};
        {| Nil |};
        {| (1, Nil) |};
        {| Cons (1, (Cons (2, Nil))) |};
        {| Cons (1, (Cons ("hi", Nil))) |};
      ];
  [%expect
    {|
    ((named_type (Unqualified list))
     (map ((a ((named_type (Unqualified int)) (map ()))))))
    (Lambda
     (Tuple
      ((TyVar a0) ((named_type (Unqualified list)) (map ((a (TyVar a0)))))))
     ((named_type (Unqualified list)) (map ((a (TyVar a0))))))
    ((named_type (Unqualified list)) (map ((a (TyVar a0)))))
    (Tuple
     (((named_type (Unqualified int)) (map ()))
      ((named_type (Unqualified list)) (map ((a (TyVar a0)))))))
    ((named_type (Unqualified list))
     (map ((a ((named_type (Unqualified int)) (map ()))))))
    (error
     ("types failed to unify" (first (Unqualified int))
      (second (Unqualified string)))) |}]

let%expect_test "if_expr" =
  infer_type_of_expr ~print_state:false ~programs:[ "if true then 1 else 0" ];
  [%expect {|
    ((named_type (Unqualified int)) (map ())) |}];
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
    ~programs:[ "if true then Cons (1, Nil) else Cons (2, Cons (1, Nil))" ];
  [%expect
    {|
    ((named_type (Unqualified list))
     (map ((a ((named_type (Unqualified int)) (map ())))))) |}]

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
    ((named_type (Unqualified int)) (map ()))
    ((named_type (Unqualified string)) (map ()))
    (error
     ("types failed to unify" (first (Unqualified int))
      (second (Unqualified list))))
    ((named_type (Unqualified int)) (map ()))
    (error
     ("types failed to unify" (first (Unqualified string))
      (second (Unqualified int)))) |}]

let%expect_test "match_expr2" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = Nil in let _ = match x with | Nil -> 1 | Cons (x, _) -> x in x |};
      ];
  [%expect
    {|
    ((named_type (Unqualified list))
     (map ((a ((named_type (Unqualified int)) (map ())))))) |}]

let%expect_test "lambda_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| (fun x -> 1) |}; {| (fun x -> 1) 1 |} ];
  [%expect
    {|
    (Lambda (TyVar a0) ((named_type (Unqualified int)) (map ())))
    ((named_type (Unqualified int)) (map ())) |}]

let%expect_test "let_expr1" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = (fun x -> 1) in x 1 |};
        {| let x = fun y -> y in x |};
        {| (fun x -> match x with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) |};
      ];
  [%expect
    {|
    ((named_type (Unqualified int)) (map ()))
    (Lambda (TyVar b0) (TyVar b0))
    (Lambda
     ((named_type (Unqualified list))
      (map ((a ((named_type (Unqualified int)) (map ()))))))
     ((named_type (Unqualified int)) (map ()))) |}]

let%expect_test "let_expr2" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = (fun y -> match y with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) in
           let y = x 1 in
           y |};
        {| let x = (fun y -> match y with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) in x |};
        {| let x = (fun y -> match y with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) in
           x (Cons ("hi", Nil)) |};
        {| let x = fun y -> match y with | Nil -> Nil | Cons (x, y) -> y in x |};
      ];
  [%expect
    {|
    (error
     ("types failed to unify" (first (Unqualified list))
      (second (Unqualified int))))
    (Lambda
     ((named_type (Unqualified list))
      (map ((a ((named_type (Unqualified int)) (map ()))))))
     ((named_type (Unqualified int)) (map ())))
    (error
     ("types failed to unify" (first (Unqualified int))
      (second (Unqualified string))))
    (Lambda ((named_type (Unqualified list)) (map ((a (TyVar e0)))))
     ((named_type (Unqualified list)) (map ((a (TyVar e0)))))) |}]

let%expect_test "let_expr3" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| let x = fun x -> (fun x -> x) (fun x -> x) x in x |} ];
  [%expect {| (Lambda (TyVar f0) (TyVar f0)) |}]

let%expect_test "let_expr_tag1" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let head = fun l default ->
             match l with
             | Nil -> default
             | Cons (x, rest) -> x
           in head |};
        {| let head = fun (l : a list) (default : a) ->
             match l with
             | Nil -> default
             | Cons (x, rest) -> x
           in head |};
        {| let head = fun (l : int) (default : a) ->
             match l with
             | Nil -> default
             | Cons (x, rest) -> x
           in head |};
        {| let head : int -> int = fun (l : int) (default : a) ->
             match l with
             | Nil -> default
             | Cons (x, rest) -> x
           in head |};
      ];
  [%expect
    {|
    (Lambda ((named_type (Unqualified list)) (map ((a (TyVar e0)))))
     (Lambda (TyVar e0) (TyVar e0)))
    (Lambda ((named_type (Unqualified list)) (map ((a (TyVar e0)))))
     (Lambda (TyVar e0) (TyVar e0)))
    (error
     ("types failed to unify" (first (Unqualified list))
      (second (Unqualified int))))
    (error "Failed to parse (b expr)") |}]

let%expect_test "type_def_record" =
  let lit =
    Ast.(
      Type_expr.(
        Qualified.(Multi (Single (Unqualified "int"), Unqualified "node"))))
  in
  let action =
    let%bind () = define_types ~type_exprs in
    type_of_type_expr lit
  in
  let res = State.Result.run action ~state:empty_state |> fst in
  print_s [%message (res : (mono, Sexp.t) Result.t)];
  [%expect
    {|
    (res
     (Ok
      (Record ((Unqualified node) ((a (Abstract ((Unqualified int) () 0)))) 1)
       ((value ((Abstract ((Unqualified int) () 0)) Immutable))
        (next
         ((Enum
           ((Unqualified option)
            ((a
              (Pointer
               (Recursive_constructor
                ((Unqualified node) ((a (Abstract ((Unqualified int) () 0)))) 0)))))
            1)
           ((None ())
            (Some
             ((Pointer
               (Recursive_constructor
                ((Unqualified node) ((a (Abstract ((Unqualified int) () 0)))) 0)))))))
          Mutable)))))) |}]

let%expect_test "last_list_record_occurs" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let last = fun f l -> match l with
            | { value : x; next : None } -> x
            | { value : _; next : Some y } -> f f y
           in last last |};
      ];
  [%expect
    {| (error ("occurs check failed" (a a0) (mono (Lambda (TyVar a0) (TyVar k0))))) |}]

let%expect_test "recursive last" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some y } -> last l
           in last |};
      ];
  [%expect
    {| (Lambda ((named_type (Unqualified node)) (map ((a (TyVar m0))))) (TyVar l0)) |}]

let%expect_test "mutual recursion" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec (-) = fun a b -> 0
           and is_even = fun x ->
             match x with
             | 0 -> true
             | _ -> is_odd (x - 1)
           and is_odd = fun x ->
             is_even (x - 1)
           in is_even |};
      ];
  [%expect
    {|
    (Lambda ((named_type (Unqualified int)) (map ()))
     ((named_type (Unqualified bool)) (map ()))) |}]

let%expect_test "mutual recursion fail" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec (-) = fun a b -> 0
           and is_even = fun x ->
             match x with
             | 0 -> true
             | _ -> is_odd (x - 1)
           and is_odd = fun x ->
             if is_even x then true else 0
           in is_even |};
      ];
  [%expect
    {|
    (error
     ("types failed to unify" (first (Unqualified bool))
      (second (Unqualified int)))) |}]

let%expect_test "recursive last not pointer" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some y } -> last l
           in last { value : 1; next : Some { value : 2; next : None } } |};
      ];
  [%expect
    {|
    (error
     ("failed to unify types"
      (first
       (Pointer (Recursive_constructor ((Unqualified node) ((a (TyVar o0))) 0))))
      (second
       (Record ((Unqualified node) ((a (TyVar q0))) 1)
        ((value ((TyVar q0) Immutable))
         (next
          ((Enum
            ((Unqualified option)
             ((a
               (Pointer
                (Recursive_constructor ((Unqualified node) ((a (TyVar q0))) 0)))))
             1)
            ((None ())
             (Some
              ((Pointer
                (Recursive_constructor ((Unqualified node) ((a (TyVar q0))) 0)))))))
           Mutable))))))) |}]

let%expect_test "recursive last value" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some y } -> last l in
           last { value : 1; next : Some &{ value : 2; next : None } } |};
      ];
  [%expect {|
    (TyVar w0) |}]

let%expect_test "node value" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| { value : 1; next : Some &{ value : 2; next : None } } |} ];
  [%expect {| ((named_type (Unqualified node)) (map ((a (TyVar a0))))) |}]

let%expect_test "node value fail" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| { value : 1; next : Some &{ value : "a"; next : None } } |} ];
  [%expect {| ((named_type (Unqualified node)) (map ((a (TyVar a0))))) |}]

let%expect_test "ref cons succ" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| Ref_cons (&1, Ref_nil) |};
        {| Ref_cons (&1, (Ref_cons (&2, Ref_nil))) |};
        {| Ref_cons |};
      ];
  [%expect
    {|
    ((named_type (Unqualified ref_list))
     (map ((a ((named_type (Unqualified int)) (map ()))))))
    ((named_type (Unqualified ref_list))
     (map ((a ((named_type (Unqualified int)) (map ()))))))
    (Lambda
     (Tuple
      ((Pointer (TyVar a0))
       ((named_type (Unqualified ref_list)) (map ((a (TyVar a0)))))))
     ((named_type (Unqualified ref_list)) (map ((a (TyVar a0)))))) |}]

let%expect_test "ref cons fl" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| Ref_cons (1, Nil) |};
        {| Ref_cons (&1, Nil) |};
        {| Ref_cons (1, Ref_nil) |};
        {| Ref_cons (&1, (Ref_cons (&"hi", Ref_nil))) |};
      ];
  [%expect
    {|
    (error
     ("failed to unify types" (first (Pointer (TyVar a0)))
      (second (Abstract ((Unqualified int) () 0)))))
    (error
     ("types failed to unify" (first (Unqualified ref_list))
      (second (Unqualified list))))
    (error
     ("failed to unify types" (first (Pointer (TyVar a0)))
      (second (Abstract ((Unqualified int) () 0)))))
    (error
     ("types failed to unify" (first (Unqualified int))
      (second (Unqualified string)))) |}]
