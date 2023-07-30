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
      add_type "int" (make_abstract "int")
      >>| Result.map_error ~f:Sexp.to_string_hum
      >>| Result.ok_or_failwith
    in
    let arg = Single_arg (Variance.Covariant, "a") in
    let mono =
      Abstract
        {
          type_name = Unqualified "list";
          ordering = Some [ "a" ];
          tyvar_map = Lowercase.Map.of_alist_exn [ ("a", TyVar "a") ];
          level = 0;
        }
    in
    add_type_constructor (Some arg) "list" mono
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
    ((res
      (Ok
       (Abstract
        ((type_name (Unqualified int)) (ordering ()) (tyvar_map ()) (level 0)))))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((int
            (()
             (Abstract
              ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
               (level 0)))))
           (list
            (((Single_arg Covariant a))
             (Abstract
              ((type_name (Unqualified list)) (ordering ((a)))
               (tyvar_map ((a (TyVar a)))) (level 0)))))))
         (toplevel_modules ())
         (opened_modules
          (((toplevel_vars
             ((& ((Forall a (Mono (Lambda (TyVar a) (Pointer (TyVar a)))))))))
            (toplevel_records ()) (toplevel_constructors ())
            (toplevel_type_constructors
             ((bool
               (()
                (Abstract
                 ((type_name (Unqualified bool)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (char
               (()
                (Abstract
                 ((type_name (Unqualified char)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (float
               (()
                (Abstract
                 ((type_name (Unqualified float)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (int
               (()
                (Abstract
                 ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (string
               (()
                (Abstract
                 ((type_name (Unqualified string)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (unit
               (()
                (Abstract
                 ((type_name (Unqualified unit)) (ordering ()) (tyvar_map ())
                  (level 0)))))))
            (toplevel_modules ()) (opened_modules ()))))))
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
        ((type_name (Unqualified list)) (ordering ((a)))
         (tyvar_map
          ((a
            (Abstract
             ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
              (level 0))))))
         (level 0)))))
     (state
      ((mono_ufds ())
       (current_module_binding
        ((toplevel_vars ()) (toplevel_records ()) (toplevel_constructors ())
         (toplevel_type_constructors
          ((int
            (()
             (Abstract
              ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
               (level 0)))))
           (list
            (((Single_arg Covariant a))
             (Abstract
              ((type_name (Unqualified list)) (ordering ((a)))
               (tyvar_map ((a (TyVar a)))) (level 0)))))))
         (toplevel_modules ())
         (opened_modules
          (((toplevel_vars
             ((& ((Forall a (Mono (Lambda (TyVar a) (Pointer (TyVar a)))))))))
            (toplevel_records ()) (toplevel_constructors ())
            (toplevel_type_constructors
             ((bool
               (()
                (Abstract
                 ((type_name (Unqualified bool)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (char
               (()
                (Abstract
                 ((type_name (Unqualified char)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (float
               (()
                (Abstract
                 ((type_name (Unqualified float)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (int
               (()
                (Abstract
                 ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (string
               (()
                (Abstract
                 ((type_name (Unqualified string)) (ordering ()) (tyvar_map ())
                  (level 0)))))
              (unit
               (()
                (Abstract
                 ((type_name (Unqualified unit)) (ordering ()) (tyvar_map ())
                  (level 0)))))))
            (toplevel_modules ()) (opened_modules ()))))))
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
       (Enum
        ((type_name (Unqualified list)) (ordering ((a)))
         (tyvar_map
          ((a
            (Abstract
             ((type_name (Unqualified int)) (ordering ()) (tyvar_map ()) (level 0))))))
         (level 1))
        ((Cons
          ((Tuple
            ((Abstract
              ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
               (level 0)))
             (Recursive_constructor
              ((type_name (Unqualified list)) (ordering ((a)))
               (tyvar_map
                ((a
                  (Abstract
                   ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
                    (level 0))))))
               (level 0)))))))
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
    {| type a nonempty_list = Nonempty_cons (a, a nonempty_list option) |};
  ]

let infer_type_of_expr ~programs ~print_state =
  let action program : unit state_result_m =
    let%bind () = define_types ~type_exprs in
    let%bind expr = Parser.try_parse Parser.parse_one program |> State.return in
    (* let%bind expr = replace_user_ty_vars expr in *)
    (* print_s [%message (expr : Ast.expr)]; *)
    let%bind mono = mono_of_expr expr in
    let%bind mono = apply_substs mono in
    let%map s = show_mono mono in
    print_endline s
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
    int list
    (a0, a0 list) -> a0 list
    a0 list
    (int, a0 list)
    int list
    (error ("types failed to unify" int string)) |}]

let%expect_test "if_expr" =
  infer_type_of_expr ~print_state:false ~programs:[ "if true then 1 else 0" ];
  [%expect {|
    int |}];
  infer_type_of_expr ~print_state:false ~programs:[ "if 1 then 1 else 0" ];
  [%expect {|
    (error ("types failed to unify" int bool)) |}];
  infer_type_of_expr ~print_state:false
    ~programs:[ "if true then \"hi\" else 0" ];
  [%expect {|
    (error ("types failed to unify" string int)) |}];
  infer_type_of_expr ~print_state:false
    ~programs:[ "if true then Cons (1, Nil) else Cons (2, Cons (1, Nil))" ];
  [%expect {|
    int list |}]

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
    int
    string
    (error ("types failed to unify" int "a0 list"))
    int
    (error ("types failed to unify" string int)) |}]

let%expect_test "match_expr2" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = Nil in let _ = match x with | Nil -> 1 | Cons (x, _) -> x in x |};
      ];
  [%expect {|
    int list |}]

let%expect_test "lambda_expr" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| (fun x -> 1) |}; {| (fun x -> 1) 1 |} ];
  [%expect {|
    a0 -> int
    int |}]

let%expect_test "let_expr1" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let x = (fun x -> 1) in x 1 |};
        {| let x = fun y -> y in x |};
        {| (fun x -> match x with | Nil -> 1 | Cons (1, Cons (2, Nil)) -> 2) |};
        {| (fun x -> match x with | Nil -> 1 | Cons (_, Cons (y, Nil)) -> y) |};
      ];
  [%expect {|
    int
    b0 -> b0
    int list -> int
    int list -> int |}]

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
    (error ("types failed to unify" "int list" int))
    int list -> int
    (error ("types failed to unify" int string))
    e0 list -> e0 list |}]

let%expect_test "let_expr3" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| let x = fun x -> (fun x -> x) (fun x -> x) x in x |} ];
  [%expect {| f0 -> f0 |}]

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
    e0 list -> e0 -> e0
    e0 list -> e0 -> e0
    (error ("types failed to unify" "c0 list" int))
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
      (Record
       ((type_name (Unqualified node)) (ordering ((a)))
        (tyvar_map
         ((a
           (Abstract
            ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
             (level 0))))))
        (level 1))
       ((value
         ((Abstract
           ((type_name (Unqualified int)) (ordering ()) (tyvar_map ()) (level 0)))
          Immutable))
        (next
         ((Enum
           ((type_name (Unqualified option)) (ordering ((a)))
            (tyvar_map
             ((a
               (Pointer
                (Recursive_constructor
                 ((type_name (Unqualified node)) (ordering ((a)))
                  (tyvar_map
                   ((a
                     (Abstract
                      ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
                       (level 0))))))
                  (level 0)))))))
            (level 1))
           ((None ())
            (Some
             ((Pointer
               (Recursive_constructor
                ((type_name (Unqualified node)) (ordering ((a)))
                 (tyvar_map
                  ((a
                    (Abstract
                     ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
                      (level 0))))))
                 (level 0))))))))
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
    {| (error ("occurs check failed" (a a0) (mono (Lambda (TyVar a0) (TyVar g0))))) |}]

let%expect_test "head nonempty list" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let id = fun x -> x in
           let head =
             fun l -> match l with
             | Nonempty_cons (x, None) -> x
             | Nonempty_cons (x, Some (Nonempty_cons (y, _))) -> id y
           in
           head |};
      ];
  [%expect {|
    j0 nonempty_list -> j0 |}]

let%expect_test "head list value" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let head =
             fun l -> match l with
             | Nonempty_cons (x, None) -> x
             | Nonempty_cons (x, Some (Nonempty_cons (y, _))) -> y
           in
           head (Nonempty_cons (1, None))|};
      ];
  [%expect {| int |}]

let%expect_test "mutual recursion" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec (-) = fun (a : int) (b : int) -> 0
           and is_even = fun x ->
             match x with
             | 0 -> true
             | _ -> is_odd (x - 1)
           and is_odd = fun x ->
             is_even (x - 1)
           in is_even |};
      ];
  [%expect {|
    int -> bool |}]

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
  [%expect {|
    (error ("types failed to unify" bool int)) |}]

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
  [%expect {|
    (error ("failed to unify types" "&i0 node" "int node")) |}]

let%expect_test "type annot1" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let id = fun (y : int) (x : string) -> x in id |};
        {| let id = fun (y : a) (x : a) -> x in id |};
        {| let id = fun (y : a) (x : a) -> x in
           id 1 "hi" |};
      ];
  [%expect
    {|
    int -> string -> string
    c0 -> c0 -> c0
    (error ("types failed to unify" int string)) |}]

let%expect_test "node value" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| { value : 1; next : Some &{ value : 2; next : None } } |} ];
  [%expect {|
    int node |}]

let%expect_test "node value fail" =
  infer_type_of_expr ~print_state:false
    ~programs:[ {| { value : 1; next : Some &{ value : "a"; next : None } } |} ];
  [%expect {|
    (error ("types failed to unify" string int)) |}]

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
    int ref_list
    int ref_list
    (&a0, a0 ref_list) -> a0 ref_list |}]

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
    (error ("failed to unify types" &a0 int))
    (error ("types failed to unify" "a0 ref_list" "d0 list"))
    (error ("failed to unify types" &a0 int))
    (error ("types failed to unify" int string)) |}]

let%expect_test "rec tail nonempty list" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec tail =
             fun l -> match l with
             | Nonempty_cons (x, None) -> x
             | Nonempty_cons (_, Some y) -> tail y
           in
           tail |};
      ];
  [%expect {|
    h0 nonempty_list -> h0 |}]

let%expect_test "rec tail list" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec tail =
             fun l -> match l with
             | Nil -> None
             | Cons (x, Nil) -> Some x
             | Cons (_, y) -> tail y
           in
           tail |};
      ];
  [%expect {|
    k0 list -> k0 option |}]

let%expect_test "rec tail nonempty list" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec tail =
             fun l -> match l with
             | Nonempty_cons (x, None) -> x
             | Nonempty_cons (_, Some y) -> tail y
           in
           tail (Nonempty_cons (1, None)) |};
      ];
  [%expect {| int |}]

let%expect_test "rec tail list value" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec tail =
             fun l -> match l with
             | Nil -> None
             | Cons (x, Nil) -> Some x
             | Cons (_, y) -> tail y
           in
           tail (Cons (1, Nil)) |};
      ];
  [%expect {|
    int option |}]

let%expect_test "head nonempty list rec needless" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let id = fun x -> x in
           let rec head =
             fun l -> match l with
             | Nonempty_cons (x, None) -> x
             | Nonempty_cons (x, Some (Nonempty_cons (y, _))) -> id y
           in
           head |};
      ];
  [%expect {|
    k0 nonempty_list -> k0 |}]

let%expect_test "record create" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let singleton =
             fun x -> { value : x; next : None }
           in
           singleton |};
      ];
  [%expect {| d0 -> d0 node |}]

let%expect_test "head record destruct" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let head =
             fun { value : x; next : _ } -> x
           in
           head |};
      ];
  [%expect {| c0 node -> c0 |}]

let%expect_test "head record value" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let head =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : x; next : Some y } -> x
           in
           head { value : 1; next : Some &{ value : 2; next : None } } |};
      ];
  [%expect {| int |}]

let%expect_test "recursive last" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some &y } -> last y
           in last |};
      ];
  [%expect {|
      i0 node -> i0 |}]

let%expect_test "recursive last value" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some &y } -> last y in
           last { value : 1; next : Some &{ value : 2; next : None } } |};
      ];
  [%expect {|
    int |}]

let%expect_test "recursive last value keeps type" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let rec last =
             fun l -> match l with
             | { value : x; next : None } -> x
             | { value : _; next : Some y } -> last l
           in
           let (=) = fun (x : string) (y : string) -> true in
           let x = last { value : 1; next : Some &{ value : 2; next : None } } in
           let y = "hi" in
           x = y |};
      ];
  [%expect {|
    (error ("types failed to unify" string int)) |}]

let%expect_test "recursive last generalizes" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {|
        let rec last = fun x ->
          match x with
          | Cons (x, Nil) -> Some x
          | Cons (_, xs) -> last xs
          | Nil -> None
        in let first = last (Cons (1, Nil)) in
        let second = last (Cons ("hi", Nil)) in
        (first, second) |};
      ];
  [%expect {|
    (int option, string option) |}]

let%expect_test "head generalizes" =
  infer_type_of_expr ~print_state:false
    ~programs:
      [
        {| let head = fun l ->
             match l with
             | Nil -> None
             | Cons (x, rest) -> Some x
           in
           let first = head (Cons (1, Nil)) in
           let second = head (Cons ("hi", Nil)) in
           (first, second) |};
      ];
  [%expect {|
    (int option, string option) |}]
