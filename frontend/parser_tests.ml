open! Core
open Parser.Parser_comb
open Parser

let print_type_expr ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run (Parser.type_expr_p ()) ~tokens in
  print_s [%message (ast : (Ast.Type_expr.t, Sexp.t) Result.t)]

let%expect_test "type_expr_single" =
  print_type_expr ~program:"int";
  [%expect {| (ast (Ok (Single (Unqualified int)))) |}]

let%expect_test "type_expr_single_extra_paren" =
  print_type_expr ~program:"int)";
  [%expect {| (ast (Ok (Single (Unqualified int)))) |}]

let%expect_test "type_expr_multi1" =
  print_type_expr ~program:"a int";
  [%expect {| (ast (Ok (Multi (Single (Unqualified a)) (Unqualified int)))) |}]

let%expect_test "type_expr_multi2" =
  print_type_expr ~program:"(a, (b int)) int d";
  [%expect
    {|
    (ast
     (Ok
      (Multi
       (Multi
        (Tuple
         ((Single (Unqualified a))
          (Multi (Single (Unqualified b)) (Unqualified int))))
        (Unqualified int))
       (Unqualified d)))) |}]

let test_parse_one ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_one ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s
    [%message (ast : (Ast.expr, Sexp.t) Result.t) (tokens : Token.t List.t)]

let%expect_test "test_function_one_arg" =
  let program = {|
       let function = fun x -> 1 in function
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Let_in
        (Nonrec ((Name function) (Lambda (Name x) (Node (Literal (Int 1))))))
        (Node (Var (Unqualified function))))))
     (tokens ())) |}]

let%expect_test "test_function_two_args_nested" =
  let program =
    {|
       let function = let y = 1 in fun x y -> 1 in function
     |}
  in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         (Let_in
          (Nonrec
           ((Name function)
            (Let_in (Nonrec ((Name y) (Node (Literal (Int 1)))))
             (Lambda (Name x) (Lambda (Name y) (Node (Literal (Int 1))))))))
          (Node (Var (Unqualified function))))))
       (tokens ())) |}]

let%expect_test "test_if_simple" =
  let program = {|
    if (true : int) then 1 else 2
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (If
        (Node
         (Wrapped
          (Unqualified
           (Typed (Node (Literal (Bool true)))
            ((type_expr (Single (Unqualified int))) (ast_tags ()))))))
        (Node (Literal (Int 1))) (Node (Literal (Int 2))))))
     (tokens ())) |}]

let%expect_test "test_app" =
  let program = {|
    1 + 2 = 3
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App
        (App (Node (Var (Unqualified =)))
         (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 1))))
          (Node (Literal (Int 2)))))
        (Node (Literal (Int 3))))))
     (tokens ())) |}]

let%expect_test "test_if_nested_application" =
  let program =
    {|
       if 1 + 2 = 3 then if false then 1 else 2 else 3
        |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (If
        (App
         (App (Node (Var (Unqualified =)))
          (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 1))))
           (Node (Literal (Int 2)))))
         (Node (Literal (Int 3))))
        (If (Node (Literal (Bool false))) (Node (Literal (Int 1)))
         (Node (Literal (Int 2))))
        (Node (Literal (Int 3))))))
     (tokens ())) |}]

let%expect_test "test_let_nested" =
  let program =
    {|
    let nested = let x = 1 in let y = 2 in x + y in nested
  |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Let_in
        (Nonrec
         ((Name nested)
          (Let_in (Nonrec ((Name x) (Node (Literal (Int 1)))))
           (Let_in (Nonrec ((Name y) (Node (Literal (Int 2)))))
            (App (App (Node (Var (Unqualified +))) (Node (Var (Unqualified x))))
             (Node (Var (Unqualified y))))))))
        (Node (Var (Unqualified nested))))))
     (tokens ())) |}]

let%expect_test "test_let_nested2" =
  let program = {|
    let x = 1 in let y = 2 in x + y
  |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Let_in (Nonrec ((Name x) (Node (Literal (Int 1)))))
        (Let_in (Nonrec ((Name y) (Node (Literal (Int 2)))))
         (App (App (Node (Var (Unqualified +))) (Node (Var (Unqualified x))))
          (Node (Var (Unqualified y))))))))
     (tokens ())) |}]

let%expect_test "test_unit_value" =
  let program = {|
    let unit = () in unit
  |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Let_in (Nonrec ((Name unit) (Node (Literal Unit))))
        (Node (Var (Unqualified unit))))))
     (tokens ())) |}]

let%expect_test "test_lots" =
  let program =
    {|
          let int = 1

          let float = 1.0

          let string = "hi"

          let bool = true

          let unit = ()

          let nested = let x = 1 in let y = 2 in x + y

          let function2 = fun x -> 1

          let function3 = fun x y -> f x + y

          let if_ = if true then 1 else 2

          let if_nested = if 1 + 2 = 3 then if false then 1 else 2 else 3
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let (Nonrec ((Name int) (Node (Literal (Int 1))))))
       (Let (Nonrec ((Name float) (Node (Literal (Float 1))))))
       (Let (Nonrec ((Name string) (Node (Literal (String hi))))))
       (Let (Nonrec ((Name bool) (Node (Literal (Bool true))))))
       (Let (Nonrec ((Name unit) (Node (Literal Unit)))))
       (Let
        (Nonrec
         ((Name nested)
          (Let_in (Nonrec ((Name x) (Node (Literal (Int 1)))))
           (Let_in (Nonrec ((Name y) (Node (Literal (Int 2)))))
            (App (App (Node (Var (Unqualified +))) (Node (Var (Unqualified x))))
             (Node (Var (Unqualified y)))))))))
       (Let
        (Nonrec ((Name function2) (Lambda (Name x) (Node (Literal (Int 1)))))))
       (Let
        (Nonrec
         ((Name function3)
          (Lambda (Name x)
           (Lambda (Name y)
            (App
             (App (Node (Var (Unqualified +)))
              (App (Node (Var (Unqualified f))) (Node (Var (Unqualified x)))))
             (Node (Var (Unqualified y)))))))))
       (Let
        (Nonrec
         ((Name if_)
          (If (Node (Literal (Bool true))) (Node (Literal (Int 1)))
           (Node (Literal (Int 2)))))))
       (Let
        (Nonrec
         ((Name if_nested)
          (If
           (App
            (App (Node (Var (Unqualified =)))
             (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 1))))
              (Node (Literal (Int 2)))))
            (Node (Literal (Int 3))))
           (If (Node (Literal (Bool false))) (Node (Literal (Int 1)))
            (Node (Literal (Int 2))))
           (Node (Literal (Int 3)))))))))) |}]

let%expect_test "test_atom_untagged" =
  let program = {| 1 |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok (Node (Literal (Int 1))))) (tokens ())) |}]

let%expect_test "test_atom_tagged" =
  let program = {| (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         (Node
          (Wrapped
           (Unqualified
            (Typed (Node (Literal (Int 1)))
             ((type_expr (Single (Unqualified int))) (ast_tags ()))))))))
       (tokens ())) |}]

let%expect_test "test_lots_type_tags" =
  let program =
    {|
    let (int : int) = (1 : int t)

    let nested = ((let x = 1 in let y = 2 in x + y) : (a, b, c) int t)

    let function2 = fun (x : string) -> (1 : int)
    let ((a, (b : int), 1) : (int, int)) = 1 |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let
        (Nonrec
         ((Typed (Name int)
           ((type_expr (Single (Unqualified int))) (ast_tags ())))
          (Node
           (Wrapped
            (Unqualified
             (Typed (Node (Literal (Int 1)))
              ((type_expr (Multi (Single (Unqualified int)) (Unqualified t)))
               (ast_tags ())))))))))
       (Let
        (Nonrec
         ((Name nested)
          (Node
           (Wrapped
            (Unqualified
             (Typed
              (Node
               (Wrapped
                (Unqualified
                 (Let_in (Nonrec ((Name x) (Node (Literal (Int 1)))))
                  (Let_in (Nonrec ((Name y) (Node (Literal (Int 2)))))
                   (App
                    (App (Node (Var (Unqualified +)))
                     (Node (Var (Unqualified x))))
                    (Node (Var (Unqualified y)))))))))
              ((type_expr
                (Multi
                 (Multi
                  (Tuple
                   ((Single (Unqualified a)) (Single (Unqualified b))
                    (Single (Unqualified c))))
                  (Unqualified int))
                 (Unqualified t)))
               (ast_tags ())))))))))
       (Let
        (Nonrec
         ((Name function2)
          (Lambda
           (Typed (Name x)
            ((type_expr (Single (Unqualified string))) (ast_tags ())))
           (Node
            (Wrapped
             (Unqualified
              (Typed (Node (Literal (Int 1)))
               ((type_expr (Single (Unqualified int))) (ast_tags ()))))))))))
       (Let
        (Nonrec
         ((Typed
           (Tuple
            (Unqualified
             ((Name a)
              (Typed (Name b)
               ((type_expr (Single (Unqualified int))) (ast_tags ())))
              (Literal (Int 1)))))
           ((type_expr
             (Tuple ((Single (Unqualified int)) (Single (Unqualified int)))))
            (ast_tags ())))
          (Node (Literal (Int 1))))))))) |}]

let%expect_test "test_apply_tags" =
  let program = {| g (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App (Node (Var (Unqualified g)))
        (Node
         (Wrapped
          (Unqualified
           (Typed (Node (Literal (Int 1)))
            ((type_expr (Single (Unqualified int))) (ast_tags ())))))))))
     (tokens ())) |}]

let%expect_test "test_apply_b" =
  let program = {| g (if 1 then 1 else 1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App (Node (Var (Unqualified g)))
        (Node
         (Wrapped
          (Unqualified
           (If (Node (Literal (Int 1))) (Node (Literal (Int 1)))
            (Typed (Node (Literal (Int 1)))
             ((type_expr (Single (Unqualified int))) (ast_tags ()))))))))))
     (tokens ())) |}]

let%expect_test "test_nested_typed_application" =
  let program = {| g (f (1 : int) (a b (c d : int) : int)) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App (Node (Var (Unqualified g)))
        (Node
         (Wrapped
          (Unqualified
           (App
            (App (Node (Var (Unqualified f)))
             (Node
              (Wrapped
               (Unqualified
                (Typed (Node (Literal (Int 1)))
                 ((type_expr (Single (Unqualified int))) (ast_tags ())))))))
            (Node
             (Wrapped
              (Unqualified
               (Typed
                (App
                 (App (Node (Var (Unqualified a))) (Node (Var (Unqualified b))))
                 (Node
                  (Wrapped
                   (Unqualified
                    (Typed
                     (App (Node (Var (Unqualified c)))
                      (Node (Var (Unqualified d))))
                     ((type_expr (Single (Unqualified int))) (ast_tags ())))))))
                ((type_expr (Single (Unqualified int))) (ast_tags ())))))))))))))
     (tokens ())) |}]

let%expect_test "test_unary_bang" =
  let program = {| 1 + !2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 1))))
        (App (Node (Var (Unqualified !))) (Node (Literal (Int 2)))))))
     (tokens ())) |}]

let%expect_test "test_apply_left_assoc" =
  let program = {| f x y |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App (App (Node (Var (Unqualified f))) (Node (Var (Unqualified x))))
        (Node (Var (Unqualified y))))))
     (tokens ())) |}]

let%expect_test "test_operator_binding" =
  let program = {|
    let (+) = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
      (ast (Ok ((Let (Nonrec ((Name +) (Node (Literal (Int 1))))))))) |}]

let%expect_test "test_operator_binding_fail" =
  let program = {|
    let + = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect {| (ast (Error ("Unexpected token" (got (Keyword let))))) |}]

let print_binding ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run (binding_p ()) ~tokens in
  print_s [%message (ast : (Ast.Binding.t, Sexp.t) Result.t)]

let%expect_test "bindings" =
  print_binding ~program:"var";
  [%expect {| (ast (Ok (Name var))) |}];
  print_binding ~program:"(+)";
  [%expect {| (ast (Ok (Name +))) |}];
  print_binding ~program:"+";
  [%expect {| (ast (Error "Expected binding")) |}]

let%expect_test "test_wrapped_addition" =
  let program = {| (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Wrapped
         (Unqualified
          (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 4))))
           (Node (Literal (Int 5)))))))))
     (tokens ())) |}]

let%expect_test "test_addition_and_times_binding" =
  let program = {| 1 * 2 + 3 * (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App
        (App (Node (Var (Unqualified +)))
         (App (App (Node (Var (Unqualified *))) (Node (Literal (Int 1))))
          (Node (Literal (Int 2)))))
        (App (App (Node (Var (Unqualified *))) (Node (Literal (Int 3))))
         (Node
          (Wrapped
           (Unqualified
            (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 4))))
             (Node (Literal (Int 5)))))))))))
     (tokens ())) |}]

let print ~parser ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parser ~tokens in
  print_s [%message (ast : (Ast.expr, Sexp.t) Result.t)]

let%expect_test "super_simple_apply" =
  let program = {| f 1 |} in
  print ~parser:(parse_pratt ()) ~program;
  [%expect
    {| (ast (Ok (App (Node (Var (Unqualified f))) (Node (Literal (Int 1)))))) |}]

let%expect_test "simple_apply" =
  let program = {| (f 1) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Wrapped
         (Unqualified
          (App (Node (Var (Unqualified f))) (Node (Literal (Int 1)))))))))
     (tokens ())) |}]

let%expect_test "simple_prefix_apply" =
  let program = {| -f |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast (Ok (App (Node (Var (Unqualified -))) (Node (Var (Unqualified f))))))
       (tokens ())) |}]

let%expect_test "simple_apply2" =
  let program = {| f 1 + 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App
        (App (Node (Var (Unqualified +)))
         (App (Node (Var (Unqualified f))) (Node (Literal (Int 1)))))
        (Node (Literal (Int 2))))))
     (tokens ())) |}]

let%expect_test "simple_apply3" =
  let program = {| f 1 - 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (App
        (App (Node (Var (Unqualified -)))
         (App (Node (Var (Unqualified f))) (Node (Literal (Int 1)))))
        (Node (Literal (Int 2))))))
     (tokens ())) |}]

let%expect_test "test_tag_p" =
  let program = {| @[type : int, mode : local, deriving : string int] |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run tag_list_p ~tokens in
  print_s [%message (ast : (Ast.Value_tag.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
       (ast_tags ((deriving ((Symbol string) (Symbol int)))))))) |}]

let%expect_test "test_tags" =
  let program = {| (f @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Wrapped
         (Unqualified
          (Typed (Node (Var (Unqualified f)))
           ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
            (ast_tags ((name ((String x))))))))))))
     (tokens ())) |}]

let%expect_test "test_tags_both" =
  let program = {| (f : string @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Wrapped
         (Unqualified
          (Typed (Node (Var (Unqualified f)))
           ((type_expr (Single (Unqualified string))) (mode (Allocation Local))
            (ast_tags ((name ((String x))))))))))))
     (tokens ())) |}]

let%expect_test "test_qualified_expr" =
  let program =
    {| Ast.B.(f : string @[type : int, mode : local, name : "x"]) |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Wrapped
         (Qualified Ast
          (Qualified B
           (Unqualified
            (Typed (Node (Var (Unqualified f)))
             ((type_expr (Single (Unqualified string))) (mode (Allocation Local))
              (ast_tags ((name ((String x))))))))))))))
     (tokens ())) |}]

let%expect_test "test_tuple_simple" =
  let program = {| (1, 2) |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         (Node
          (Tuple (Unqualified ((Node (Literal (Int 1))) (Node (Literal (Int 2)))))))))
       (tokens ())) |}]

let%expect_test "test_tuples" =
  let program =
    {|
          let (int : (int, int)) = (1, 2)

          let nested = (let x = 1 in let y = 2 in x + y, fun x -> 2, (1 : int))
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let
        (Nonrec
         ((Typed (Name int)
           ((type_expr
             (Tuple ((Single (Unqualified int)) (Single (Unqualified int)))))
            (ast_tags ())))
          (Node
           (Tuple
            (Unqualified ((Node (Literal (Int 1))) (Node (Literal (Int 2))))))))))
       (Let
        (Nonrec
         ((Name nested)
          (Node
           (Tuple
            (Unqualified
             ((Let_in (Nonrec ((Name x) (Node (Literal (Int 1)))))
               (Let_in (Nonrec ((Name y) (Node (Literal (Int 2)))))
                (App
                 (App (Node (Var (Unqualified +))) (Node (Var (Unqualified x))))
                 (Node (Var (Unqualified y))))))
              (Lambda (Name x) (Node (Literal (Int 2))))
              (Node
               (Wrapped
                (Unqualified
                 (Typed (Node (Literal (Int 1)))
                  ((type_expr (Single (Unqualified int))) (ast_tags ())))))))))))))))) |}]

let%expect_test "test_pattern_binding" =
  let program =
    {|
          let Cons a = _

          let Cons = _

          let Ast.Cons a = _

          let Ast.Cons (a) = _

          let Ast.(Cons) (a, (Pee e as x), c) = _

          let (Ast.Cons (Ast.Cons a) as y) = _

          let { a : b; c : (d, e) } = _

          let (1, 2) = (1, 2)
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let
        (Nonrec
         ((Constructor (Unqualified Cons) ((Name a)))
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Constructor (Unqualified Cons) ()) (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Constructor (Qualified Ast (Unqualified Cons)) ((Name a)))
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Constructor (Qualified Ast (Unqualified Cons)) ((Name a)))
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Constructor (Qualified Ast (Unqualified Cons))
           ((Tuple
             (Unqualified
              ((Name a) (Renamed (Constructor (Unqualified Pee) ((Name e))) x)
               (Name c))))))
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Renamed
           (Constructor (Qualified Ast (Unqualified Cons))
            ((Constructor (Qualified Ast (Unqualified Cons)) ((Name a)))))
           y)
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Record
           (Unqualified
            ((a (Name b)) (c (Tuple (Unqualified ((Name d) (Name e))))))))
          (Node (Var (Unqualified _))))))
       (Let
        (Nonrec
         ((Tuple (Unqualified ((Literal (Int 1)) (Literal (Int 2)))))
          (Node
           (Tuple
            (Unqualified ((Node (Literal (Int 1))) (Node (Literal (Int 2))))))))))))) |}]

let%expect_test "test_type_define" =
  let program =
    {|
         type (+a, -b) c = A a | B (b, c) @[cool]

         type t = a list

         type record = { a : int; mutable b : (string, int) } @[cringe: false]
       |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_t ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t) (tokens : Token.t list)];
  [%expect
    {|
    ((ast
      (Ok
       ((Type_def
         ((type_name (Poly ((Tuple ((Covariant a) (Contravariant b))) c)))
          (type_def
           (Enum
            ((A ((Single (Unqualified a))))
             (B ((Tuple ((Single (Unqualified b)) (Single (Unqualified c)))))))))
          (ast_tags ((cool ())))))
        (Type_def
         ((type_name (Mono t))
          (type_def
           (Type_expr (Multi (Single (Unqualified a)) (Unqualified list))))
          (ast_tags ())))
        (Type_def
         ((type_name (Mono record))
          (type_def
           (Record
            ((a ((Single (Unqualified int)) Immutable))
             (b
              ((Tuple ((Single (Unqualified string)) (Single (Unqualified int))))
               Mutable)))))
          (ast_tags ((cringe ((Bool false))))))))))
     (tokens ())) |}]

let%expect_test "test_match" =
  let program = {|
      match 1 with
      | Cons a -> a
      | Nil -> 1 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Match (Node (Literal (Int 1)))
        (((Constructor (Unqualified Cons) ((Name a)))
          (Node (Var (Unqualified a))))
         ((Constructor (Unqualified Nil) ()) (Node (Literal (Int 1))))))))
     (tokens ())) |}]

let%expect_test "test_type_expr_no_paren" =
  let program = {| a b c : int |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Typed
        (App (App (Node (Var (Unqualified a))) (Node (Var (Unqualified b))))
         (Node (Var (Unqualified c))))
        ((type_expr (Single (Unqualified int))) (ast_tags ())))))
     (tokens ())) |}]

let%expect_test "type_expr_pointer" =
  print_type_expr ~program:"&int";
  [%expect {| (ast (Ok (Pointer (Single (Unqualified int))))) |}]

let%expect_test "type_expr_pointer_multi" =
  print_type_expr ~program:"&int a";
  [%expect
    {|
    (ast (Ok (Multi (Pointer (Single (Unqualified int))) (Unqualified a)))) |}]

let%expect_test "type_expr_pointer_paren" =
  print_type_expr ~program:"&(int a)";
  [%expect
    {|
    (ast (Ok (Pointer (Multi (Single (Unqualified int)) (Unqualified a))))) |}]

let%expect_test "type_expr_multi_pointer" =
  print_type_expr ~program:"& & &int";
  [%expect
    {| (ast (Ok (Pointer (Pointer (Pointer (Single (Unqualified int))))))) |}]

let%expect_test "test_infix_spaces" =
  let program = {| a b c + Cons t |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         (App
          (App (Node (Var (Unqualified +)))
           (App (App (Node (Var (Unqualified a))) (Node (Var (Unqualified b))))
            (Node (Var (Unqualified c)))))
          (App (Node (Constructor (Unqualified Cons)))
           (Node (Var (Unqualified t)))))))
       (tokens ())) |}]

let%expect_test "test_double_tag" =
  let program = {| 4 : int @[mode: local] |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Typed (Node (Literal (Int 4)))
        ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
         (ast_tags ())))))
     (tokens ())) |}]

let%expect_test "test_tuple" =
  let program = {| (1, if p = 2 then 3 else 4 : int @[mode: local]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Tuple
         (Unqualified
          ((Node (Literal (Int 1)))
           (If
            (App (App (Node (Var (Unqualified =))) (Node (Var (Unqualified p))))
             (Node (Literal (Int 2))))
            (Node (Literal (Int 3)))
            (Typed (Node (Literal (Int 4)))
             ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
              (ast_tags ()))))))))))
     (tokens ())) |}]

let%expect_test "test_record" =
  let program =
    {| { x : 1; y: if p = 2 then 3 else 4 : int @[mode: local]} |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Node
        (Record
         (Unqualified
          ((x (Node (Literal (Int 1))))
           (y
            (If
             (App (App (Node (Var (Unqualified =))) (Node (Var (Unqualified p))))
              (Node (Literal (Int 2))))
             (Node (Literal (Int 3)))
             (Typed (Node (Literal (Int 4)))
              ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
               (ast_tags ())))))))))))
     (tokens ())) |}]

let%expect_test "test_constructor_with_infix" =
  let program =
    {| Cons 1 + 2 + { x : 1; y: if p = 2 then 3 else 4 : int @[mode: local]} |}
  in
  test_parse_one ~program;
  [%expect
    {|
  ((ast
    (Ok
     (App
      (App (Node (Var (Unqualified +)))
       (App
        (App (Node (Var (Unqualified +)))
         (App (Node (Constructor (Unqualified Cons))) (Node (Literal (Int 1)))))
        (Node (Literal (Int 2)))))
      (Node
       (Record
        (Unqualified
         ((x (Node (Literal (Int 1))))
          (y
           (If
            (App
             (App (Node (Var (Unqualified =))) (Node (Var (Unqualified p))))
             (Node (Literal (Int 2))))
            (Node (Literal (Int 3)))
            (Typed (Node (Literal (Int 4)))
             ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
              (ast_tags ()))))))))))))
   (tokens ())) |}]

let%expect_test "test_exp_binding" =
  let program = {| 1 + &2 * 3**2 * (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
  ((ast
    (Ok
     (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 1))))
      (App
       (App (Node (Var (Unqualified *)))
        (App
         (App (Node (Var (Unqualified *)))
          (App (Node (Var (Unqualified &))) (Node (Literal (Int 2)))))
         (App (App (Node (Var (Unqualified **))) (Node (Literal (Int 3))))
          (Node (Literal (Int 2))))))
       (Node
        (Wrapped
         (Unqualified
          (App (App (Node (Var (Unqualified +))) (Node (Literal (Int 4))))
           (Node (Literal (Int 5)))))))))))
   (tokens ())) |}]

let%expect_test "test_type_define_enum" =
  let program = {| type a list = Cons (a, &(a list)) | Nil |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_t ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t) (tokens : Token.t list)];
  [%expect
    {|
    ((ast
      (Ok
       ((Type_def
         ((type_name (Poly ((Single (Invariant a)) list)))
          (type_def
           (Enum
            ((Cons
              ((Tuple
                ((Single (Unqualified a))
                 (Pointer (Multi (Single (Unqualified a)) (Unqualified list)))))))
             (Nil ()))))
          (ast_tags ()))))))
     (tokens ())) |}]

let%expect_test "test_match" =
  let program =
    {|
      match Cons 1 with
      | Cons a -> a
      | Nil -> 1 |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Match
        (App (Node (Constructor (Unqualified Cons))) (Node (Literal (Int 1))))
        (((Constructor (Unqualified Cons) ((Name a)))
          (Node (Var (Unqualified a))))
         ((Constructor (Unqualified Nil) ()) (Node (Literal (Int 1))))))))
     (tokens ())) |}]

let%expect_test "rec one" =
  let program =
    {| let rec last =
         fun l -> match l with
         | { value : x; next : None } -> x
         | { value : _; next : Some y } -> last l
       in last |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       (Let_in
        (Rec
         (((Name last)
           (Lambda (Name l)
            (Match (Node (Var (Unqualified l)))
             (((Record
                (Unqualified
                 ((next (Constructor (Unqualified None) ())) (value (Name x)))))
               (Node (Var (Unqualified x))))
              ((Record
                (Unqualified
                 ((next (Constructor (Unqualified Some) ((Name y))))
                  (value (Name _)))))
               (App (Node (Var (Unqualified last))) (Node (Var (Unqualified l)))))))))))
        (Node (Var (Unqualified last))))))
     (tokens ())) |}]

let%expect_test "rec two" =
  let program =
    {| let rec last_node =
         fun l -> match l with
         | ({ value : _; next : None } as p) -> value p
         | { value : _; next : Some y } -> last_node y
       and value = fun x -> match x with | { value : value; next : next } -> value
       in last_node |}
  in
  test_parse_one ~program;
  [%expect {|
    ((ast
      (Ok
       (Let_in
        (Rec
         (((Name last_node)
           (Lambda (Name l)
            (Match (Node (Var (Unqualified l)))
             (((Renamed
                (Record
                 (Unqualified
                  ((next (Constructor (Unqualified None) ())) (value (Name _)))))
                p)
               (App (Node (Var (Unqualified value)))
                (Node (Var (Unqualified p)))))
              ((Record
                (Unqualified
                 ((next (Constructor (Unqualified Some) ((Name y))))
                  (value (Name _)))))
               (App (Node (Var (Unqualified last_node)))
                (Node (Var (Unqualified y)))))))))
          ((Name value)
           (Lambda (Name x)
            (Match (Node (Var (Unqualified x)))
             (((Record (Unqualified ((next (Name next)) (value (Name value)))))
               (Node (Var (Unqualified value))))))))))
        (Node (Var (Unqualified last_node))))))
     (tokens ())) |}]

let%expect_test "rec toplevel" =
  let program =
    {|
        let rec g = fun x -> f (x - 1)
        and f = fun x -> x + 1
       |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_t ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t) (tokens : Token.t list)];
  [%expect
    {|
    ((ast
      (Ok
       ((Let
         (Rec
          (((Name g)
            (Lambda (Name x)
             (App (Node (Var (Unqualified f)))
              (Node
               (Wrapped
                (Unqualified
                 (App
                  (App (Node (Var (Unqualified -))) (Node (Var (Unqualified x))))
                  (Node (Literal (Int 1))))))))))
           ((Name f)
            (Lambda (Name x)
             (App (App (Node (Var (Unqualified +))) (Node (Var (Unqualified x))))
              (Node (Literal (Int 1))))))))))))
     (tokens ())) |}]
