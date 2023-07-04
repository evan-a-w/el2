open! Core

module Parse_state = struct
  type 'a t = ('a, Sexp.t, Token.t List.t) Result_state.t

  include (
    Result_state :
      module type of Result_state
        with type ('a, 'b, 'c) t := ('a, 'b, 'c) Result_state.t)

  let end_of_input = stop [%message "Unexpected end of input"]

  let next : Token.t t =
    let open Let_syntax in
    let%bind tokens = get in
    match tokens with
    | [] -> end_of_input
    | token :: tokens ->
        let%bind () = put tokens in
        return token
end

open Parse_state
open Parse_state.Let_syntax

let match_token ~expected got =
  match Token.compare got expected with
  | 0 -> return ()
  | _ -> stop [%message (expected : Token.t) (got : Token.t)]

let rec parse tokens = ()

and parse_lambda tokens =
  let%bind () = match_token ~expected:LParen tokens in
  ()

and parse_atom =
  match%bind next with
  | Token.Int x -> Ast.Int x |> return
  | Float f -> Ast.Float f |> return
  | Bool b -> Ast.Bool b |> return
  | String s -> Ast.String s |> return
  | Identifer s -> Ast.Var s |> return
  | got -> stop [%message "Expected atom" (got : Token.t)]
