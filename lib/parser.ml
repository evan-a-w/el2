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
    match%bind.State p with
    | Ok res -> loop (res :: acc)
    | Error _ -> return acc
  in
  loop []

let take_while p = take_while_rev p >>| List.rev

let get_symbol : String.t parser =
  let%bind token = next in
  match token with
  | Symbol s -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

(* need unit to let stuff work because of weird ocaml rules that I didn't bother to understand *)
let rec parse () : Ast.t parser =
  first
    [ parse_lambda (); parse_let_in (); parse_let (); parse_if (); parse_atom ]
  |> map_error ~f:(fun errors ->
         [%message "Failed to parse" (errors : Sexp.t List.t)])

and parse_lambda () =
  let%bind () = eat_token LParen in
  let%bind idents = take_while_rev get_symbol in
  let%bind () = eat_token RParen in
  let%bind () = eat_token Arrow in
  let%bind expr = parse () in
  match idents with
  | [] -> return (Ast.Lambda (None, expr))
  | x :: xs ->
      let init = Ast.Lambda (Some x, expr) in
      let lambda =
        List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (Some x, acc))
      in
      return lambda

and parse_let () =
  let%bind () = eat_token (Token.Symbol "let") in
  let%bind var = get_symbol in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse () in
  return (Ast.Let (var, expr))

and parse_let_in () =
  match%bind parse_let () with
  | Ast.Let (var, expr) ->
      let%bind () = eat_token (Token.Symbol "in") in
      let%bind body = parse () in
      return (Ast.Let_in (var, expr, body))
  | _ -> failwith "parse_let returned non Ast.Let node"

and parse_if () =
  let%bind () = eat_token (Token.Symbol "if") in
  let%bind cond = parse () in
  let%bind () = eat_token (Token.Symbol "then") in
  let%bind then_ = parse () in
  let%bind () = eat_token (Token.Symbol "else") in
  let%bind else_ = parse () in
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
