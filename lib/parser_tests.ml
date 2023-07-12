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
  [%expect
    {| (ast (Ok (Multi ((Single (Unqualified a))) (Single (Unqualified int))))) |}]

let%expect_test "type_expr_multi2" =
  print_type_expr ~program:"(a, (b int)) int d";
  [%expect
    {|
    (ast
     (Ok
      (Multi
       ((Single (Unqualified a))
        (Multi ((Single (Unqualified b))) (Single (Unqualified int))))
       (Multi ((Single (Unqualified int))) (Single (Unqualified d)))))) |}]

let test_parse_one ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_one ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t) (tokens : Token.t List.t)]

let%expect_test "test_function_one_arg" =
  let program = {|
       let function = fun x -> 1 in function
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Let (function ()) ((node (Lambda (x ()) ((node (Int 1))))))
          ((node (Var (Unqualified (function ()))))))))))
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
         ((node
           (Let (function ())
            ((node
              (Let (y ()) ((node (Int 1)))
               ((node (Lambda (x ()) ((node (Lambda (y ()) ((node (Int 1))))))))))))
            ((node (Var (Unqualified (function ()))))))))))
       (tokens ())) |}]

let%expect_test "test_if_simple" =
  let program = {|
    if true then 1 else 2
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok ((node (If ((node (Bool true))) ((node (Int 1))) ((node (Int 2))))))))
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
       ((node
         (App
          (App (Var (Unqualified (= ())))
           (App (App (Var (Unqualified (+ ()))) (Int 1)) (Int 2)))
          (Int 3))))))
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
       ((node
         (If
          ((node
            (App
             (App (Var (Unqualified (= ())))
              (App (App (Var (Unqualified (+ ()))) (Int 1)) (Int 2)))
             (Int 3))))
          ((node (If ((node (Bool false))) ((node (Int 1))) ((node (Int 2))))))
          ((node (Int 3))))))))
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
       ((node
         (Let (nested ())
          ((node
            (Let (x ()) ((node (Int 1)))
             ((node
               (Let (y ()) ((node (Int 2)))
                ((node
                  (App
                   (App (Var (Unqualified (+ ()))) (Var (Unqualified (x ()))))
                   (Var (Unqualified (y ()))))))))))))
          ((node (Var (Unqualified (nested ()))))))))))
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
       ((node
         (Let (x ()) ((node (Int 1)))
          ((node
            (Let (y ()) ((node (Int 2)))
             ((node
               (App (App (Var (Unqualified (+ ()))) (Var (Unqualified (x ()))))
                (Var (Unqualified (y ()))))))))))))))
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
       ((node
         (Let (unit ()) ((node Unit)) ((node (Var (Unqualified (unit ()))))))))))
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
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      (((int ()) ((node (Int 1)))) ((float ()) ((node (Float 1))))
       ((string ()) ((node (String hi)))) ((bool ()) ((node (Bool true))))
       ((unit ()) ((node Unit)))
       ((nested ())
        ((node
          (Let (x ()) ((node (Int 1)))
           ((node
             (Let (y ()) ((node (Int 2)))
              ((node
                (App (App (Var (Unqualified (+ ()))) (Var (Unqualified (x ()))))
                 (Var (Unqualified (y ())))))))))))))
       ((function2 ()) ((node (Lambda (x ()) ((node (Int 1)))))))
       ((function3 ())
        ((node
          (Lambda (x ())
           ((node
             (Lambda (y ())
              ((node
                (App
                 (App (Var (Unqualified (+ ())))
                  (App (Var (Unqualified (f ()))) (Var (Unqualified (x ())))))
                 (Var (Unqualified (y ())))))))))))))
       ((if_ ())
        ((node (If ((node (Bool true))) ((node (Int 1))) ((node (Int 2)))))))
       ((if_nested ())
        ((node
          (If
           ((node
             (App
              (App (Var (Unqualified (= ())))
               (App (App (Var (Unqualified (+ ()))) (Int 1)) (Int 2)))
              (Int 3))))
           ((node (If ((node (Bool false))) ((node (Int 1))) ((node (Int 2))))))
           ((node (Int 3)))))))))) |}]

let%expect_test "test_atom_untagged" =
  let program = {| 1 |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok ((node (Int 1))))) (tokens ())) |}]

let%expect_test "test_atom_tagged" =
  let program = {| (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast (Ok ((tag ((type_expr (Single (Unqualified int))))) (node (Int 1)))))
       (tokens ())) |}]

let%expect_test "test_lots_type_tags" =
  let program =
    {|
    let (int : int) = (1 : int t)

    let nested = ((let x = 1 in let y = 2 in x + y) : (a, b, c) int t)

    let function2 = fun (x : string) -> (1 : int) |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      (((int (((type_expr (Single (Unqualified int))))))
        ((tag
          ((type_expr
            (Multi ((Single (Unqualified int))) (Single (Unqualified t))))))
         (node (Int 1))))
       ((nested ())
        ((tag
          ((type_expr
            (Multi
             ((Single (Unqualified a)) (Single (Unqualified b))
              (Single (Unqualified c)))
             (Multi ((Single (Unqualified int))) (Single (Unqualified t)))))))
         (node
          (Wrapped
           (Unqualified
            ((node
              (Let (x ()) ((node (Int 1)))
               ((node
                 (Let (y ()) ((node (Int 2)))
                  ((node
                    (App
                     (App (Var (Unqualified (+ ()))) (Var (Unqualified (x ()))))
                     (Var (Unqualified (y ())))))))))))))))))
       ((function2 ())
        ((node
          (Lambda (x (((type_expr (Single (Unqualified string))))))
           ((tag ((type_expr (Single (Unqualified int))))) (node (Int 1)))))))))) |}]

let%expect_test "test_apply_tags" =
  let program = {| g (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (g ())))
          (Wrapped
           (Unqualified
            ((tag ((type_expr (Single (Unqualified int))))) (node (Int 1))))))))))
     (tokens ())) |}]

let%expect_test "test_apply_b" =
  let program = {| g (if 1 then 1 else 1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (g ())))
          (Wrapped
           (Unqualified
            ((tag ((type_expr (Single (Unqualified int)))))
             (node (If ((node (Int 1))) ((node (Int 1))) ((node (Int 1)))))))))))))
     (tokens ())) |}]

let%expect_test "test_nested_typed_application" =
  let program = {| g (f (1 : int) (a b (c d : int) : int)) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (g ())))
          (Wrapped
           (Unqualified
            ((node
              (App
               (App (Var (Unqualified (f ())))
                (Wrapped
                 (Unqualified
                  ((tag ((type_expr (Single (Unqualified int))))) (node (Int 1))))))
               (Wrapped
                (Unqualified
                 ((tag ((type_expr (Single (Unqualified int)))))
                  (node
                   (App
                    (App (Var (Unqualified (a ()))) (Var (Unqualified (b ()))))
                    (Wrapped
                     (Unqualified
                      ((tag ((type_expr (Single (Unqualified int)))))
                       (node
                        (App (Var (Unqualified (c ())))
                         (Var (Unqualified (d ())))))))))))))))))))))))
     (tokens ())) |}]

let%expect_test "test_unary_bang" =
  let program = {| 1 + !2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (App (Var (Unqualified (+ ()))) (Int 1))
          (App (Var (Unqualified (! ()))) (Int 2)))))))
     (tokens ())) |}]

let%expect_test "test_apply_left_assoc" =
  let program = {| f x y |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (App (Var (Unqualified (f ()))) (Var (Unqualified (x ()))))
          (Var (Unqualified (y ()))))))))
     (tokens ())) |}]

let%expect_test "test_operator_binding" =
  let program = {|
    let (+) = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect {| (ast (Ok (((+ ()) ((node (Int 1))))))) |}]

let%expect_test "test_operator_binding_fail" =
  let program = {|
    let + = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect {| (ast (Error ("Unexpected token" (got (Keyword let))))) |}]

let print_binding ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run binding_p ~tokens in
  print_s [%message (ast : (Ast.binding, Sexp.t) Result.t)]

let%expect_test "bindings" =
  print_binding ~program:"var";
  [%expect {| (ast (Ok (var ()))) |}];
  print_binding ~program:"(+)";
  [%expect {| (ast (Ok (+ ()))) |}];
  print_binding ~program:"+";
  [%expect {| (ast (Error ("Expected binding" (got (Symbol +))))) |}]

let%expect_test "test_wrapped_addition" =
  let program = {| (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Wrapped
          (Unqualified
           ((node (App (App (Var (Unqualified (+ ()))) (Int 4)) (Int 5))))))))))
     (tokens ())) |}]

let%expect_test "test_addition_and_times_binding" =
  let program = {| 1 * 2 + 3 * (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App
          (App (Var (Unqualified (+ ())))
           (App (App (Var (Unqualified (* ()))) (Int 1)) (Int 2)))
          (App (App (Var (Unqualified (* ()))) (Int 3))
           (Wrapped
            (Unqualified
             ((node (App (App (Var (Unqualified (+ ()))) (Int 4)) (Int 5))))))))))))
     (tokens ())) |}]

let print ~parser ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parser ~tokens in
  print_s [%message (ast : (Ast.node, Sexp.t) Result.t)]

let%expect_test "super_simple_apply" =
  let program = {| f 1 |} in
  print ~parser:(parse_pratt ()) ~program;
  [%expect {| (ast (Ok (App (Var (Unqualified (f ()))) (Int 1)))) |}]

let%expect_test "simple_apply" =
  let program = {| (f 1) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Wrapped
          (Unqualified ((node (App (Var (Unqualified (f ()))) (Int 1))))))))))
     (tokens ())) |}]

let%expect_test "simple_prefix_apply" =
  let program = {| -f |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok ((node (App (Var (Unqualified (- ()))) (Var (Unqualified (f ()))))))))
       (tokens ())) |}]

let%expect_test "simple_apply2" =
  let program = {| f 1 + 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App
          (App (Var (Unqualified (+ ())))
           (App (Var (Unqualified (f ()))) (Int 1)))
          (Int 2))))))
     (tokens ())) |}]

let%expect_test "simple_apply3" =
  let program = {| f 1 - 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App
          (App (Var (Unqualified (- ())))
           (App (Var (Unqualified (f ()))) (Int 1)))
          (Int 2))))))
     (tokens ())) |}]

let%expect_test "test_tag_p" =
  let program = {| @[type : int, mode : local, deriving : string int] |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run tag_list_p ~tokens in
  print_s [%message (ast : (Ast.Tag.t, Sexp.t) Result.t)];
  [%expect
    {|
      (ast
       (Ok
        ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
         (others ((deriving ((Symbol string) (Symbol int)))))))) |}]

let%expect_test "test_tags" =
  let program = {| (f @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((tag
         ((type_expr (Single (Unqualified int))) (mode (Allocation Local))
          (others ((name ((String x)))))))
        (node (Var (Unqualified (f ())))))))
     (tokens ())) |}]

let%expect_test "test_tags_both" =
  let program = {| (f : string @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((tag
         ((type_expr (Single (Unqualified string))) (mode (Allocation Local))
          (others ((name ((String x)))))))
        (node (Var (Unqualified (f ())))))))
     (tokens ())) |}]

let%expect_test "test_qualifed_expr" =
  let program =
    {| Ast.B.(f : string @[type : int, mode : local, name : "x"]) |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Var
          (Qualified Ast
           (Qualified B
            (Unqualified
             (f
              (((type_expr (Single (Unqualified string)))
                (mode (Allocation Local)) (others ((name ((String x))))))))))))))))
     (tokens ())) |}]
