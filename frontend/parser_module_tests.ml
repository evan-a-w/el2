open! Core
open! Parser.Parser_comb
open! Parser

let%expect_test "test_simple_module" =
  let program =
    {|
      module X = struct
        let x = 1
        let y = 2

        type t = int string

        module Y = struct
           let y = 2
        end
      end
   |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Module_def
        (module_description ((module_name X) (functor_args ()) (module_sig ())))
        (module_def
         (Struct
          ((Let (Nonrec ((Name x) (Node (Literal (Int 1))))))
           (Let (Nonrec ((Name y) (Node (Literal (Int 2))))))
           (Type_def
            ((type_name (Mono t))
             (type_def
              (Type_expr (Multi (Single (Unqualified int)) (Unqualified string))))
             (ast_tags ())))
           (Module_def
            (module_description
             ((module_name Y) (functor_args ()) (module_sig ())))
            (module_def
             (Struct ((Let (Nonrec ((Name y) (Node (Literal (Int 2))))))))))))))))) |}]
;;

let%expect_test "test_simple_module_with_sig" =
  let program =
    {|
      module X : sig
        let x : int
        let y : int

        type t

        module Y : sig
           let y : int
        end
      end = struct
        let x = 1
        let y = 2

        type t = int string

        module Y = struct
           let y = 2
        end
      end
   |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Module_def
        (module_description
         ((module_name X) (functor_args ())
          (module_sig
           (((Sig_binding (Name x)
              ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (Sig_binding (Name y)
              ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (Sig_type_def ((type_name (Mono t)) (type_def ()) (ast_tags ())))
             (Sig_module
              ((module_name Y) (functor_args ())
               (module_sig
                ((Sig_binding (Name y)
                  ((type_expr (Single (Unqualified int))) (ast_tags ()))))))))))))
        (module_def
         (Struct
          ((Let (Nonrec ((Name x) (Node (Literal (Int 1))))))
           (Let (Nonrec ((Name y) (Node (Literal (Int 2))))))
           (Type_def
            ((type_name (Mono t))
             (type_def
              (Type_expr (Multi (Single (Unqualified int)) (Unqualified string))))
             (ast_tags ())))
           (Module_def
            (module_description
             ((module_name Y) (functor_args ()) (module_sig ())))
            (module_def
             (Struct ((Let (Nonrec ((Name y) (Node (Literal (Int 2))))))))))))))))) |}]
;;

let%expect_test "test_functor" =
  let program =
    {|
      module X (Arg : sig type t let x : t end) : sig
        let x : Arg.t
        let y : int

        type t

        module Y : sig
           let y : int
        end
      end = struct
        let x = Arg.x
        let y = 2

        type t = int string

        module Y = struct
           let y = 2
        end
      end
   |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Module_def
        (module_description
         ((module_name X)
          (functor_args
           ((Arg
             ((Sig_type_def ((type_name (Mono t)) (type_def ()) (ast_tags ())))
              (Sig_binding (Name x)
               ((type_expr (Single (Unqualified t))) (ast_tags ())))))))
          (module_sig
           (((Sig_binding (Name x)
              ((type_expr (Single (Qualified Arg (Unqualified t))))
               (ast_tags ())))
             (Sig_binding (Name y)
              ((type_expr (Single (Unqualified int))) (ast_tags ())))
             (Sig_type_def ((type_name (Mono t)) (type_def ()) (ast_tags ())))
             (Sig_module
              ((module_name Y) (functor_args ())
               (module_sig
                ((Sig_binding (Name y)
                  ((type_expr (Single (Unqualified int))) (ast_tags ()))))))))))))
        (module_def
         (Struct
          ((Let (Nonrec ((Name x) (Node (Var (Qualified Arg (Unqualified x)))))))
           (Let (Nonrec ((Name y) (Node (Literal (Int 2))))))
           (Type_def
            ((type_name (Mono t))
             (type_def
              (Type_expr (Multi (Single (Unqualified int)) (Unqualified string))))
             (ast_tags ())))
           (Module_def
            (module_description
             ((module_name Y) (functor_args ()) (module_sig ())))
            (module_def
             (Struct ((Let (Nonrec ((Name y) (Node (Literal (Int 2))))))))))))))))) |}]
;;

let%expect_test "test_named_module_functor_app" =
  let program =
    {|
      module X = Y (Arg1) (Arg2 : sig type t #[deriving: sexp] let x : int end)
   |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Module_def
        (module_description ((module_name X) (functor_args ()) (module_sig ())))
        (module_def
         (Functor_app (Unqualified Y)
          ((Named (Unqualified Arg1))
           (Module_typed (Named (Unqualified Arg2))
            ((Sig_type_def
              ((type_name (Mono t)) (type_def ())
               (ast_tags ((deriving ((Symbol sexp)))))))
             (Sig_binding (Name x)
              ((type_expr (Single (Unqualified int))) (ast_tags ())))))))))))) |}]
;;
