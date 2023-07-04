open! Core

let match_token ~expected got =
  match Token.compare got expected with
  | 0 -> Ok ()
  | _ -> Or_error.error_s [%message (expected : Token.t) (got : Token.t)]

let rec parse tokens = ()
and parse_lambda tokens =
  let%bind () = match_token ~expected:LParen tokens in
and parse_atom (token : Token.t) : Ast.t Or_error.t =
  match token with
  | Token.Int x -> Ast.Int x |> Or_error.return
  | Float f -> Ast.Float f |> Or_error.return
  | Bool b -> Ast.Bool b |> Or_error.return
  | String s -> Ast.String s |> Or_error.return
  | Unit -> Ast.Unit |> Or_error.return
  | Identifer s -> Ast.Var s |> Or_error.return
  | got -> Or_error.error_s [%message "Expected atom" (got : Token.t)]
