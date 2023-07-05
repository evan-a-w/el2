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

let take_while_rev (type a) (p : a parser) : a List.t parser =
  let rec loop acc =
    let%bind prev_state = get in
    match%bind.State p with
    | Ok res -> loop (res :: acc)
    | Error _ ->
        let%bind () = put prev_state in
        return acc
  in
  loop []

let take_while p = take_while_rev p >>| List.rev

let get_identifier : String.t parser =
  let%bind token = next in
  match token with
  | Symbol s -> return s
  | got -> error [%message "Expected identifier" (got : Token.t)]

let rec parse_a () : Ast.t parser =
  first [ parse_atom; parse_in_paren () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_b () =
  first
    [
      parse_lambda (); parse_let_in (); parse_if (); parse_apply (); parse_a ();
    ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])

and parse_one () = parse_let () <|> parse_b ()

and parse_in_paren () =
  let%bind () = eat_token LParen in
  let%bind expr = parse_b () in
  let%bind () = eat_token RParen in
  return expr

and parse_lambda () =
  let%bind () = eat_token LParen in
  let%bind idents = take_while_rev get_identifier in
  let%bind () = eat_token RParen in
  let%bind () = eat_token Arrow in
  let%bind expr = parse_a () in
  match idents with
  | [] -> return (Ast.Lambda (None, expr))
  | x :: xs ->
      let init = Ast.Lambda (Some x, expr) in
      let lambda =
        List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (Some x, acc))
      in
      return lambda

and parse_let () =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind var = get_identifier in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse_b () in
  return (Ast.Let (var, expr))

and parse_let_in () =
  match%bind parse_let () with
  | Ast.Let (var, expr) ->
      let%bind () = eat_token (Token.Keyword "in") in
      let%bind body = parse_b () in
      return (Ast.Let_in (var, expr, body))
  | _ -> failwith "parse_let returned non Ast.Let node"

and parse_if () =
  let%bind () = eat_token (Token.Keyword "if") in
  let%bind cond = parse_b () in
  let%bind () = eat_token (Token.Keyword "then") in
  let%bind then_ = parse_b () in
  let%bind () = eat_token (Token.Keyword "else") in
  let%bind else_ = parse_b () in
  return (Ast.If (cond, then_, else_))

and parse_atom =
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

and parse_apply () =
  match%bind take_while (parse_a ()) with
  | a :: b :: rest ->
      let init = Ast.App (a, b) in
      let res = List.fold rest ~init ~f:(fun acc x -> Ast.App (acc, x)) in
      return res
  | _ -> error [%message "Expected one or more expressions"]

let parse =
  let%bind program = take_while (parse_one ()) in
  let%bind tokens = get in
  match tokens with
  | [] -> return program
  | got -> error [%message "Unexpected tokens" (got : Token.t List.t)]

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
       let function = let y = 1 in (x y) -> 1
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

          let function3 = (x y) -> f x + y

          let if_ = if true then 1 else 2

          let if_nested = if 1 + 2 = 3 then if false then 1 else 2 else 3
        |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~state:tokens in
  print_s [%message (ast : (Ast.t List.t, Sexp.t) Result.t)];
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
