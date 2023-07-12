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
    {| (ast (Ok (Multi (Single (Unqualified a)) (Single (Unqualified int))))) |}]

let%expect_test "type_expr_multi2" =
  print_type_expr ~program:"(a, (b int)) int d";
  [%expect
    {|
    (ast
     (Ok
      (Multi
       (Tuple
        (Unqualified
         ((Single (Unqualified a))
          (Multi (Single (Unqualified b)) (Single (Unqualified int))))))
       (Multi (Single (Unqualified int)) (Single (Unqualified d)))))) |}]

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
         (Let (Name function)
          ((node (Lambda (Name x) ((node (Literal (Int 1)))))))
          ((node (Var (Unqualified (Name function))))))))))
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
           (Let (Name function)
            ((node
              (Let (Name y) ((node (Literal (Int 1))))
               ((node
                 (Lambda (Name x)
                  ((node (Lambda (Name y) ((node (Literal (Int 1)))))))))))))
            ((node (Var (Unqualified (Name function))))))))))
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
       ((node
         (If
          ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
           (node (Literal (Bool true))))
          ((node (Literal (Int 1)))) ((node (Literal (Int 2)))))))))
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
          (App (Var (Unqualified (Name =)))
           (App (App (Var (Unqualified (Name +))) (Literal (Int 1)))
            (Literal (Int 2))))
          (Literal (Int 3)))))))
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
             (App (Var (Unqualified (Name =)))
              (App (App (Var (Unqualified (Name +))) (Literal (Int 1)))
               (Literal (Int 2))))
             (Literal (Int 3)))))
          ((node
            (If ((node (Literal (Bool false)))) ((node (Literal (Int 1))))
             ((node (Literal (Int 2)))))))
          ((node (Literal (Int 3)))))))))
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
         (Let (Name nested)
          ((node
            (Let (Name x) ((node (Literal (Int 1))))
             ((node
               (Let (Name y) ((node (Literal (Int 2))))
                ((node
                  (App
                   (App (Var (Unqualified (Name +)))
                    (Var (Unqualified (Name x))))
                   (Var (Unqualified (Name y))))))))))))
          ((node (Var (Unqualified (Name nested))))))))))
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
         (Let (Name x) ((node (Literal (Int 1))))
          ((node
            (Let (Name y) ((node (Literal (Int 2))))
             ((node
               (App
                (App (Var (Unqualified (Name +))) (Var (Unqualified (Name x))))
                (Var (Unqualified (Name y))))))))))))))
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
         (Let (Name unit) ((node (Literal Unit)))
          ((node (Var (Unqualified (Name unit))))))))))
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
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let (binding (Name int)) (expr ((node (Literal (Int 1))))))
       (Let (binding (Name float)) (expr ((node (Literal (Float 1))))))
       (Let (binding (Name string)) (expr ((node (Literal (String hi))))))
       (Let (binding (Name bool)) (expr ((node (Literal (Bool true))))))
       (Let (binding (Name unit)) (expr ((node (Literal Unit)))))
       (Let (binding (Name nested))
        (expr
         ((node
           (Let (Name x) ((node (Literal (Int 1))))
            ((node
              (Let (Name y) ((node (Literal (Int 2))))
               ((node
                 (App
                  (App (Var (Unqualified (Name +))) (Var (Unqualified (Name x))))
                  (Var (Unqualified (Name y))))))))))))))
       (Let (binding (Name function2))
        (expr ((node (Lambda (Name x) ((node (Literal (Int 1)))))))))
       (Let (binding (Name function3))
        (expr
         ((node
           (Lambda (Name x)
            ((node
              (Lambda (Name y)
               ((node
                 (App
                  (App (Var (Unqualified (Name +)))
                   (App (Var (Unqualified (Name f)))
                    (Var (Unqualified (Name x)))))
                  (Var (Unqualified (Name y))))))))))))))
       (Let (binding (Name if_))
        (expr
         ((node
           (If ((node (Literal (Bool true)))) ((node (Literal (Int 1))))
            ((node (Literal (Int 2)))))))))
       (Let (binding (Name if_nested))
        (expr
         ((node
           (If
            ((node
              (App
               (App (Var (Unqualified (Name =)))
                (App (App (Var (Unqualified (Name +))) (Literal (Int 1)))
                 (Literal (Int 2))))
               (Literal (Int 3)))))
            ((node
              (If ((node (Literal (Bool false)))) ((node (Literal (Int 1))))
               ((node (Literal (Int 2)))))))
            ((node (Literal (Int 3)))))))))))) |}]

let%expect_test "test_atom_untagged" =
  let program = {| 1 |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok ((node (Literal (Int 1)))))) (tokens ())) |}]

let%expect_test "test_atom_tagged" =
  let program = {| (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
          (node (Literal (Int 1))))))
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
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let
        (binding
         (Typed (Name int)
          ((type_expr (Single (Unqualified int))) (ast_tags ()))))
        (expr
         ((tag
           ((type_expr
             (Multi (Single (Unqualified int)) (Single (Unqualified t))))
            (ast_tags ())))
          (node (Literal (Int 1))))))
       (Let (binding (Name nested))
        (expr
         ((tag
           ((type_expr
             (Multi
              (Tuple
               (Unqualified
                ((Single (Unqualified a)) (Single (Unqualified b))
                 (Single (Unqualified c)))))
              (Multi (Single (Unqualified int)) (Single (Unqualified t)))))
            (ast_tags ())))
          (node
           (Wrapped
            (Unqualified
             ((node
               (Let (Name x) ((node (Literal (Int 1))))
                ((node
                  (Let (Name y) ((node (Literal (Int 2))))
                   ((node
                     (App
                      (App (Var (Unqualified (Name +)))
                       (Var (Unqualified (Name x))))
                      (Var (Unqualified (Name y))))))))))))))))))
       (Let (binding (Name function2))
        (expr
         ((node
           (Lambda
            (Typed (Name x)
             ((type_expr (Single (Unqualified string))) (ast_tags ())))
            ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (node (Literal (Int 1)))))))))
       (Let
        (binding
         (Typed
          (Tuple
           (Unqualified
            ((Name a)
             (Typed (Name b)
              ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (Literal (Int 1)))))
          ((type_expr
            (Tuple
             (Unqualified
              ((Single (Unqualified int)) (Single (Unqualified int))))))
           (ast_tags ()))))
        (expr ((node (Literal (Int 1))))))))) |}]

let%expect_test "test_apply_tags" =
  let program = {| g (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (Name g)))
          (Wrapped
           (Unqualified
            ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (node (Literal (Int 1)))))))))))
     (tokens ())) |}]

let%expect_test "test_apply_b" =
  let program = {| g (if 1 then 1 else 1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (Name g)))
          (Wrapped
           (Unqualified
            ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (node
              (If ((node (Literal (Int 1)))) ((node (Literal (Int 1))))
               ((node (Literal (Int 1))))))))))))))
     (tokens ())) |}]

let%expect_test "test_nested_typed_application" =
  let program = {| g (f (1 : int) (a b (c d : int) : int)) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (Unqualified (Name g)))
          (Wrapped
           (Unqualified
            ((node
              (App
               (App (Var (Unqualified (Name f)))
                (Wrapped
                 (Unqualified
                  ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
                   (node (Literal (Int 1)))))))
               (Wrapped
                (Unqualified
                 ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
                  (node
                   (App
                    (App (Var (Unqualified (Name a)))
                     (Var (Unqualified (Name b))))
                    (Wrapped
                     (Unqualified
                      ((tag
                        ((type_expr (Single (Unqualified int))) (ast_tags ())))
                       (node
                        (App (Var (Unqualified (Name c)))
                         (Var (Unqualified (Name d)))))))))))))))))))))))
     (tokens ())) |}]

let%expect_test "test_unary_bang" =
  let program = {| 1 + !2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (App (Var (Unqualified (Name +))) (Literal (Int 1)))
          (App (Var (Unqualified (Name !))) (Literal (Int 2))))))))
     (tokens ())) |}]

let%expect_test "test_apply_left_assoc" =
  let program = {| f x y |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (App (Var (Unqualified (Name f))) (Var (Unqualified (Name x))))
          (Var (Unqualified (Name y))))))))
     (tokens ())) |}]

let%expect_test "test_operator_binding" =
  let program = {|
    let (+) = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
  [%expect
    {| (ast (Ok ((Let (binding (Name +)) (expr ((node (Literal (Int 1))))))))) |}]

let%expect_test "test_operator_binding_fail" =
  let program = {|
    let + = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
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
       ((node
         (Wrapped
          (Unqualified
           ((node
             (App (App (Var (Unqualified (Name +))) (Literal (Int 4)))
              (Literal (Int 5)))))))))))
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
          (App (Var (Unqualified (Name +)))
           (App (App (Var (Unqualified (Name *))) (Literal (Int 1)))
            (Literal (Int 2))))
          (App (App (Var (Unqualified (Name *))) (Literal (Int 3)))
           (Wrapped
            (Unqualified
             ((node
               (App (App (Var (Unqualified (Name +))) (Literal (Int 4)))
                (Literal (Int 5)))))))))))))
     (tokens ())) |}]

let print ~parser ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parser ~tokens in
  print_s [%message (ast : (Ast.node, Sexp.t) Result.t)]

let%expect_test "super_simple_apply" =
  let program = {| f 1 |} in
  print ~parser:(parse_pratt ()) ~program;
  [%expect
    {| (ast (Ok (App (Var (Unqualified (Name f))) (Literal (Int 1))))) |}]

let%expect_test "simple_apply" =
  let program = {| (f 1) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Wrapped
          (Unqualified
           ((node (App (Var (Unqualified (Name f))) (Literal (Int 1)))))))))))
     (tokens ())) |}]

let%expect_test "simple_prefix_apply" =
  let program = {| -f |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok
         ((node (App (Var (Unqualified (Name -))) (Var (Unqualified (Name f))))))))
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
          (App (Var (Unqualified (Name +)))
           (App (Var (Unqualified (Name f))) (Literal (Int 1))))
          (Literal (Int 2)))))))
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
          (App (Var (Unqualified (Name -)))
           (App (Var (Unqualified (Name f))) (Literal (Int 1))))
          (Literal (Int 2)))))))
     (tokens ())) |}]

let%expect_test "test_tag_p" =
  let program = {| @[type : int, mode : local, deriving : string int] |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run tag_list_p ~tokens in
  print_s [%message (ast : (Ast.Value_tag.t, Sexp.t) Result.t)];
  [%expect {|
      (ast (Error ((expected RBrack) (got (Keyword type))))) |}]

let%expect_test "test_tags" =
  let program = {| (f @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Error "Failed to parse (b expr)"))
     (tokens
      (LParen (Symbol f) At LBrack (Keyword type) Colon (Symbol int) Comma
       (Symbol mode) Colon (Symbol local) Comma (Symbol name) Colon (String x)
       RBrack RParen))) |}]

let%expect_test "test_tags_both" =
  let program = {| (f : string @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Error "Failed to parse (b expr)"))
     (tokens
      (LParen (Symbol f) Colon (Symbol string) At LBrack (Keyword type) Colon
       (Symbol int) Comma (Symbol mode) Colon (Symbol local) Comma (Symbol name)
       Colon (String x) RBrack RParen))) |}]

let%expect_test "test_qualifed_expr" =
  let program =
    {| Ast.B.(f : string @[type : int, mode : local, name : "x"]) |}
  in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Error "Failed to parse (b expr)"))
     (tokens
      ((Symbol Ast) Dot (Symbol B) Dot LParen (Symbol f) Colon (Symbol string) At
       LBrack (Keyword type) Colon (Symbol int) Comma (Symbol mode) Colon
       (Symbol local) Comma (Symbol name) Colon (String x) RBrack RParen))) |}]

let%expect_test "test_tuple_simple" =
  let program = {| (1, 2) |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok ((node (Tuple (Unqualified ((Literal (Int 1)) (Literal (Int 2)))))))))
       (tokens ())) |}]

let%expect_test "test_tuples" =
  let program =
    {|
          let (int : (int, int)) = (1, 2)

          let nested = (let x = 1 in let y = 2 in x + y, fun x -> 2, (1 : int))
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let
        (binding
         (Typed (Name int)
          ((type_expr
            (Tuple
             (Unqualified
              ((Single (Unqualified int)) (Single (Unqualified int))))))
           (ast_tags ()))))
        (expr
         ((node (Tuple (Unqualified ((Literal (Int 1)) (Literal (Int 2)))))))))
       (Let (binding (Name nested))
        (expr
         ((node
           (Tuple
            (Unqualified
             ((Let (Name x) ((node (Literal (Int 1))))
               ((node
                 (Let (Name y) ((node (Literal (Int 2))))
                  ((node
                    (App
                     (App (Var (Unqualified (Name +)))
                      (Var (Unqualified (Name x))))
                     (Var (Unqualified (Name y))))))))))
              (Lambda (Name x) ((node (Literal (Int 2)))))
              (Wrapped
               (Unqualified
                ((tag ((type_expr (Single (Unqualified int))) (ast_tags ())))
                 (node (Literal (Int 1)))))))))))))))) |}]

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
  let ast, _ = run parse_toplevel ~tokens in
  print_s [%message (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let (binding (Constructor (Unqualified Cons) ((Name a))))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let (binding (Constructor (Unqualified Cons) ()))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let (binding (Constructor (Qualified Ast (Unqualified Cons)) ((Name a))))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let (binding (Constructor (Qualified Ast (Unqualified Cons)) ((Name a))))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let
        (binding
         (Constructor (Qualified Ast (Unqualified Cons))
          ((Tuple
            (Unqualified
             ((Name a) (Renamed (Constructor (Unqualified Pee) ((Name e))) x)
              (Name c)))))))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let
        (binding
         (Renamed
          (Constructor (Qualified Ast (Unqualified Cons))
           ((Constructor (Qualified Ast (Unqualified Cons)) ((Name a)))))
          y))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let
        (binding
         (Record
          (Unqualified
           ((a (Name b)) (c (Tuple (Unqualified ((Name d) (Name e)))))))))
        (expr ((node (Var (Unqualified (Name _)))))))
       (Let (binding (Tuple (Unqualified ((Literal (Int 1)) (Literal (Int 2))))))
        (expr
         ((node (Tuple (Unqualified ((Literal (Int 1)) (Literal (Int 2)))))))))))) |}]

let%expect_test "test_type_define" =
  let program =
    {|
         type a b c = A a | B (b, c)

         type t = a list

         type rec = { a : int; b : (string, int) }
       |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_toplevel ~tokens in
  let tokens = Sequence.to_list tokens in
  print_s
    [%message
      (ast : (Ast.Toplevel.t List.t, Sexp.t) Result.t) (tokens : Token.t list)];
  [%expect
    {|
    ((ast
      (Ok
       ((Type_def
         (name
          (Multi (Single (Unqualified a))
           (Multi (Single (Unqualified b)) (Single (Unqualified c)))))
         (expr
          (Enum
           ((A ((Single (Unqualified a))))
            (B
             ((Tuple
               (Unqualified ((Single (Unqualified b)) (Single (Unqualified c)))))))))))
        (Type_def (name (Single (Unqualified t)))
         (expr
          (Type_expr
           (Multi (Single (Unqualified a)) (Single (Unqualified list))))))
        (Type_def (name (Single (Unqualified rec)))
         (expr
          (Record
           ((a (Single (Unqualified int)))
            (b
             (Tuple
              (Unqualified
               ((Single (Unqualified string)) (Single (Unqualified int)))))))))))))
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
       ((node
         (Match ((node (Literal (Int 1))))
          (((Constructor (Unqualified Cons) ((Name a)))
            ((node (Var (Unqualified (Name a))))))
           ((Constructor (Unqualified Nil) ()) ((node (Literal (Int 1)))))))))))
     (tokens ())) |}]

let%expect_test "test_constructor_with_infix" =
  let program = {| Cons 1 + 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Error "Failed to parse (b expr)"))
     (tokens ((Symbol Cons) (Int 1) (Symbol +) (Int 2)))) |}]

let%expect_test "test_type_expr_no_paren" =
  let program = {| a b c : int |} in
  test_parse_one ~program;
  [%expect {|
    ((ast
      (Ok
       ((node
         (App (App (Var (Unqualified (Name a))) (Var (Unqualified (Name b))))
          (Var (Unqualified (Name c))))))))
     (tokens (Colon (Symbol int)))) |}]
