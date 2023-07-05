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
  let%bind first = p in
  let%bind prev_state = get in
  match%bind.State sep with
  | Error _ ->
      let%bind () = put prev_state in
      return [ first ]
  | Ok _ ->
      let%bind rest = many_sep_rev p ~sep in
      return (first :: rest)

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
    let%bind res = many_sep_rev1 (b ()) ~sep:(eat_token Token.Comma) in
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
  let%bind () = eat_token (Token.Symbol ":") in
  type_expr_p ()

let rec parse_a_tagged () : Ast.t parser =
  let%bind () = eat_token LParen in
  let%bind node =
    first [ parse_atom; parse_in_paren () ]
    |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])
  in
  let%bind prev_state = get in
  let%bind ast =
    match%bind.State type_tag_p with
    | Ok type_expr -> return { Ast.node; type_expr = Some type_expr }
    | Error _ ->
        let%bind () = put prev_state in
        return { Ast.node; type_expr = None }
  in
  let%bind () = eat_token RParen in
  return ast

and parse_a_untagged () : Ast.t parser =
  let%bind node =
    first [ parse_atom; parse_in_paren () ]
    |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])
  in
  return { Ast.node; type_expr = None }

and parse_a () : Ast.t parser = parse_a_tagged () <|> parse_a_untagged ()

and parse_b () : Ast.t parser =
  match%bind.State parse_a () with
  | Ok _ as a -> State.return a
  | _ ->
      first [ parse_lambda (); parse_let_in (); parse_if (); parse_apply () ]
      |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])

and parse_one () = parse_b ()

and parse_in_paren () : Ast.node parser =
  let%bind () = eat_token LParen in
  let%bind expr = parse_b () in
  let%bind () = eat_token RParen in
  return (Ast.Wrapped expr)

and parse_lambda () : Ast.t parser =
  let%bind () = eat_token LParen in
  let%bind idents = many_sep_rev1 get_identifier ~sep:(eat_token Token.Comma) in
  let%bind () = eat_token RParen in
  let%bind () = eat_token Arrow in
  let%bind expr = parse_a () in
  match idents with
  | [] -> assert false
  | x :: xs ->
      let init = Ast.Lambda (x, expr) |> Ast.untyped in
      let lambda =
        List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (x, acc) |> Ast.untyped)
      in
      return lambda

and parse_let () : (string * Ast.t) parser =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind var = get_identifier in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse_b () in
  return (var, expr)

and parse_let_in () : Ast.t parser =
  let%bind var, expr = parse_let () in
  let%bind () = eat_token (Token.Keyword "in") in
  let%bind body = parse_b () in
  return (Ast.Let_in (var, expr, body) |> Ast.untyped)

and parse_if () : Ast.t parser =
  let%bind () = eat_token (Token.Keyword "if") in
  let%bind cond = parse_b () in
  let%bind () = eat_token (Token.Keyword "then") in
  let%bind then_ = parse_b () in
  let%bind () = eat_token (Token.Keyword "else") in
  let%bind else_ = parse_b () in
  return (Ast.If (cond, then_, else_) |> Ast.untyped)

and parse_atom : Ast.node parser =
  match%bind next with
  | Token.Int x -> Ast.Int x |> return
  | Float f -> Ast.Float f |> return
  | Bool b -> Ast.Bool b |> return
  | String s -> Ast.String s |> return
  | Symbol s -> Ast.Var s |> return
  | LParen ->
      let%bind () = eat_token RParen in
      return Ast.Unit
  | got -> error [%message "Expected atom" (got : Token.t)]

and parse_apply () : Ast.t parser =
  match%bind many (parse_a ()) with
  | a :: b :: rest ->
      let init = Ast.App (a, b) |> Ast.untyped in
      let res =
        List.fold rest ~init ~f:(fun acc x -> Ast.App (acc, x) |> Ast.untyped)
      in
      return res
  | _ -> error [%message "Expected one or more expressions"]

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

let%expect_test "type_expr_single" = print_type_expr ~program:"int"
let%expect_test "type_expr_multi1" = print_type_expr ~program:"a int"

let%expect_test "type_expr_multi2" =
  print_type_expr ~program:"(a, (b int)) int d"

let test_parse_one ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, tokens = run (parse_one ()) ~state:tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t) (tokens : Token.t List.t)]

let%expect_test "test_function_no_args" =
  let program = {|
    let function = () -> 1
  |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok (Let function (Lambda () (Int 1))))) (tokens ())) |}]

let%expect_test "test_function_one_arg" =
  let program = {|
       let function = (x) -> 1
     |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok (Let function (Lambda (x) (Int 1))))) (tokens ())) |}]

let%expect_test "test_function_two_args_nested" =
  let program = {|
       let function = let y = 1 in (x, y) -> 1
     |} in
  test_parse_one ~program;
  [%expect
    {|
      ((ast
        (Ok (Let function (Let_in y (Int 1) (Lambda (x) (Lambda (y) (Int 1)))))))
       (tokens ())) |}]

let%expect_test "test_if_simple" =
  let program = {|
    if true then 1 else 2
     |} in
  test_parse_one ~program;
  [%expect {| ((ast (Ok (If (Bool true) (Int 1) (Int 2)))) (tokens ())) |}]

let%expect_test "test_app" =
  let program = {|
    1 + 2 = 3
     |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Ok (App (App (App (App (Int 1) (Var +)) (Int 2)) (Var =)) (Int 3))))
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
       (If (App (App (App (App (Int 1) (Var +)) (Int 2)) (Var =)) (Int 3))
        (If (Bool false) (Int 1) (Int 2)) (Int 3))))
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

          let function = () -> 1

          let function2 = (x) -> 1

          let function3 = (x, y) -> f x + y

          let if_ = if true then 1 else 2

          let if_nested = if 1 + 2 = 3 then if false then 1 else 2 else 3
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~state:tokens in
  print_s [%message (ast : ((string, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      ((Let int (Int 1)) (Let float (Float 1)) (Let string (String hi))
       (Let bool (Bool true)) (Let unit Unit)
       (Let nested
        (Let_in x (Int 1) (Let_in y (Int 2) (App (App (Var x) (Var +)) (Var y)))))
       (Let function (Lambda () (Int 1))) (Let function2 (Lambda (x) (Int 1)))
       (Let function3 (Lambda (x) (Lambda (y) (Var f))))
       (App (App (Var x) (Var +)) (Var y))
       (Let if_ (If (Bool true) (Int 1) (Int 2)))
       (Let if_nested
        (If (App (App (App (App (Int 1) (Var +)) (Int 2)) (Var =)) (Int 3))
         (If (Bool false) (Int 1) (Int 2)) (Int 3)))))) |}]
