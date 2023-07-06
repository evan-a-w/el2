open! Core

module Parse_state = struct
  include State.Result

  type 'a t = ('a, Sexp.t, Token.t List.t) State.Result.t

  let end_of_input = error [%message "Unexpected end of input"]

  let next : Token.t t =
    let open Let_syntax in
    let%bind tokens = get in
    match tokens with
    | [] -> end_of_input
    | token :: tokens ->
        let%bind () = put tokens in
        return token

  let put_back token =
    let open Let_syntax in
    let%bind tokens = get in
    put (token :: tokens)
end

open Parse_state
open Parse_state.Let_syntax

type 'a parser = 'a t

let eat_token expected =
  let%bind got = next in
  match Token.compare got expected with
  | 0 -> return ()
  | _ -> error [%message (expected : Token.t) (got : Token.t)]

let many_sep_rev p ~sep =
  let rec loop acc =
    let%bind prev_state = get in
    match%bind.State p with
    | Error _ ->
        let%bind () = put prev_state in
        return acc
    | Ok res -> (
        let%bind prev_state = get in
        match%bind.State sep with
        | Ok _ -> loop (res :: acc)
        | Error _ ->
            let%bind () = put prev_state in
            return (res :: acc))
  in
  loop []

let many_sep p ~sep = many_sep_rev p ~sep >>| List.rev
let many_rev p = many_sep_rev p ~sep:(return ())

let many_sep_rev1 p ~sep =
  let%bind ps = many_sep_rev p ~sep in
  match ps with
  | [] -> error [%message "Expected at least one element"]
  | _ :: _ -> return ps

let many_rev1 p = many_sep_rev1 p ~sep:(return ())
let many_sep1 p ~sep = many_sep_rev1 p ~sep >>| List.rev
let many p = many_sep p ~sep:(return ())

let get_identifier : String.t parser =
  let%bind token = next in
  match token with
  | Symbol s -> return s
  | got -> error [%message "Expected identifier" (got : Token.t)]

let type_expr_p () : Types.Type_expr.t parser =
  let rec single = get_identifier >>| Types.Type_expr.single
  and paren () =
    let%bind () = eat_token LParen in
    let%bind res = b () in
    let%bind () = eat_token RParen in
    return res
  and a () = single <|> paren ()
  and list () =
    let%bind () = eat_token Token.LParen in
    let%bind res = many_sep1 (b ()) ~sep:(eat_token Token.Comma) in
    let%bind () = eat_token Token.RParen in
    return res
  and multi () =
    let single_f = single >>| fun x -> [ x ] in
    let%bind first = single_f <|> list () in
    let%bind next = b () in
    return (Types.Type_expr.Multi (first, next))
  and b () = multi () <|> a () in
  b ()

let type_tag_p : Types.Type_expr.t parser =
  let%bind () = eat_token Token.Colon in
  type_expr_p ()

let parse_tagged p =
  let%bind () = eat_token LParen in
  let%bind inner = p in
  let%bind type_expr = type_tag_p in
  let%bind () = eat_token RParen in
  return (inner, type_expr)

let parse_maybe_tagged p =
  let fst =
    let%bind a, b = parse_tagged p in
    return (a, Some b)
  in
  let snd = p >>| fun x -> (x, None) in
  fst <|> snd

let binding_p = parse_maybe_tagged get_identifier

let rec parse_a () : Ast.node parser =
  first [ parse_atom; parse_in_paren () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_a_tagged () : Ast.t parser =
  let%bind node, type_expr = parse_maybe_tagged (parse_a ()) in
  return { Ast.node; type_expr }

and parse_b () : Ast.t parser =
  let inner =
    first
      [
        parse_lambda ();
        parse_let_in ();
        parse_if ();
        parse_apply ();
        parse_a ();
      ]
    |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])
  in
  let%bind node, type_expr = parse_maybe_tagged inner in
  return { Ast.node; type_expr }

and parse_in_paren () : Ast.node parser =
  let%bind () = eat_token LParen in
  let%bind expr = parse_b () in
  let%bind () = eat_token RParen in
  return (Ast.Wrapped expr)

and parse_lambda () : Ast.node parser =
  let%bind () = eat_token (Token.Keyword "fun") in
  let%bind bindings = many_rev1 binding_p in
  let%bind () = eat_token Arrow in
  let%bind expr = parse_b () in
  match bindings with
  | [] -> assert false
  | x :: xs ->
      let init = Ast.Lambda (x, expr) in
      let lambda =
        List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (x, Ast.untyped acc))
      in
      return lambda

and parse_let () : (Ast.binding * Ast.t) parser =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind binding = binding_p in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse_b () in
  return (binding, expr)

and parse_let_in () : Ast.node parser =
  let%bind var, expr = parse_let () in
  let%bind () = eat_token (Token.Keyword "in") in
  let%bind body = parse_b () in
  return (Ast.Let (var, expr, body))

and parse_if () : Ast.node parser =
  let%bind () = eat_token (Token.Keyword "if") in
  let%bind cond = parse_b () in
  let%bind () = eat_token (Token.Keyword "then") in
  let%bind then_ = parse_b () in
  let%bind () = eat_token (Token.Keyword "else") in
  let%bind else_ = parse_b () in
  return (Ast.If (cond, then_, else_))

and parse_atom : Ast.node parser =
  let non_binding =
    match%bind next with
    | Token.Int x -> Ast.Int x |> return
    | Float f -> Ast.Float f |> return
    | Bool b -> Ast.Bool b |> return
    | String s -> Ast.String s |> return
    | LParen ->
        let%bind () = eat_token RParen in
        return Ast.Unit
    | got -> error [%message "Expected atom" (got : Token.t)]
  in
  let binding = binding_p >>| fun x -> Ast.Var x in
  non_binding <|> binding

and parse_apply () : Ast.node parser =
  match%bind many (parse_a_tagged ()) with
  | a :: b :: rest ->
      let init = Ast.App (a, b) in
      let res =
        List.fold rest ~init ~f:(fun acc x -> Ast.App (Ast.untyped acc, x))
      in
      return res
  | _ -> error [%message "Expected one or more expressions"]

let parse_one = parse_b ()

let parse =
  let%bind program = many (parse_let ()) in
  let%bind tokens = get in
  match tokens with
  | [] -> return program
  | got -> error [%message "Unexpected tokens" (got : Token.t List.t)]

let print_type_expr ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run (type_expr_p ()) ~state:tokens in
  print_s [%message (ast : (Types.Type_expr.t, Sexp.t) Result.t)]

let%expect_test "type_expr_single" =
  print_type_expr ~program:"int";
  [%expect {| (ast (Ok (Single int))) |}]

let%expect_test "type_expr_single_extra_paren" =
  print_type_expr ~program:"int)";
  [%expect {| (ast (Ok (Single int))) |}]

let%expect_test "type_expr_multi1" =
  print_type_expr ~program:"a int";
  [%expect {| (ast (Ok (Multi ((Single a)) (Single int)))) |}]

let%expect_test "type_expr_multi2" =
  print_type_expr ~program:"(a, (b int)) int d";
  [%expect
    {|
    (ast
     (Ok
      (Multi ((Single a) (Multi ((Single b)) (Single int)))
       (Multi ((Single int)) (Single d))))) |}]

let test_parse_one ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run parse_one ~state:tokens in
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
          ((node (Var (function ())))))))))
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
            ((node (Var (function ())))))))))
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
          ((node
            (App
             ((node
               (App ((node (App ((node (Int 1))) ((node (Var (+ ())))))))
                ((node (Int 2))))))
             ((node (Var (= ())))))))
          ((node (Int 3))))))))
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
             ((node
               (App
                ((node
                  (App ((node (App ((node (Int 1))) ((node (Var (+ ())))))))
                   ((node (Int 2))))))
                ((node (Var (= ())))))))
             ((node (Int 3))))))
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
                  (App ((node (App ((node (Var (x ())))) ((node (Var (+ ())))))))
                   ((node (Var (y ())))))))))))))
          ((node (Var (nested ())))))))))
     (tokens ())) |}]

let%expect_test "test_unit_value" =
  let program = {|
    let unit = () in unit
  |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Ok ((node (Let (unit ()) ((node Unit)) ((node (Var (unit ())))))))))
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
  let ast, _ = run parse ~state:tokens in
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
                (App ((node (App ((node (Var (x ())))) ((node (Var (+ ())))))))
                 ((node (Var (y ()))))))))))))))
       ((function2 ()) ((node (Lambda (x ()) ((node (Int 1)))))))
       ((function3 ())
        ((node
          (Lambda (x ())
           ((node
             (Lambda (y ())
              ((node
                (App
                 ((node
                   (App
                    ((node (App ((node (Var (f ())))) ((node (Var (x ())))))))
                    ((node (Var (+ ())))))))
                 ((node (Var (y ()))))))))))))))
       ((if_ ())
        ((node (If ((node (Bool true))) ((node (Int 1))) ((node (Int 2)))))))
       ((if_nested ())
        ((node
          (If
           ((node
             (App
              ((node
                (App
                 ((node
                   (App ((node (App ((node (Int 1))) ((node (Var (+ ())))))))
                    ((node (Int 2))))))
                 ((node (Var (= ())))))))
              ((node (Int 3))))))
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
    {| ((ast (Ok ((type_expr (Single int)) (node (Int 1))))) (tokens ())) |}]

let%expect_test "test_lots_type_tags" =
  let program =
    {|
    let (int : int) = (1 : int t)

    let nested = ((let x = 1 in let y = 2 in x + y) : (a, b, c) int t)

    let function2 = fun (x : string) -> (1 : int) |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~state:tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      (((int ((Single int)))
        ((type_expr (Multi ((Single int)) (Single t))) (node (Int 1))))
       ((nested ())
        ((type_expr
          (Multi ((Single a) (Single b) (Single c))
           (Multi ((Single int)) (Single t))))
         (node
          (Wrapped
           ((node
             (Let (x ()) ((node (Int 1)))
              ((node
                (Let (y ()) ((node (Int 2)))
                 ((node
                   (App
                    ((node (App ((node (Var (x ())))) ((node (Var (+ ())))))))
                    ((node (Var (y ())))))))))))))))))
       ((function2 ())
        ((node
          (Lambda (x ((Single string)))
           ((type_expr (Single int)) (node (Int 1)))))))))) |}]

let%expect_test "test_apply_tags" =
  let program = {| g (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App ((node (Var (g ())))) ((type_expr (Single int)) (node (Int 1))))))))
     (tokens ())) |}]

let%expect_test "test_nested_typed_application" =
  let program = {| g (f (1 : int) (a b (c d : int) : int)) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Ok ((node (Var (g ()))))))
     (tokens
      (LParen (Symbol f) LParen (Int 1) Colon (Symbol int) RParen LParen
       (Symbol a) (Symbol b) LParen (Symbol c) (Symbol d) Colon (Symbol int)
       RParen Colon (Symbol int) RParen RParen))) |}]
