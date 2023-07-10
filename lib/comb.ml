open! Core

module type S = sig
  type t [@@deriving compare, sexp]
end

module Make (Token : S) = struct
  include State.Result
  open Let_syntax

  type 'result parser = ('result, Sexp.t, Token.t Sequence.t) State.Result.t

  let end_of_input = error [%message "Unexpected end of input"]

  let next =
    let open Let_syntax in
    let%bind tokens = get in
    match Sequence.next tokens with
    | None -> end_of_input
    | Some (token, tokens) ->
        let%bind () = put tokens in
        return token

  let next_opt : Token.t Option.t parser =
    let open Let_syntax in
    let%bind tokens = get in
    match Sequence.next tokens with
    | None -> return None
    | Some (token, tokens) ->
        let%bind () = put tokens in
        return (Some token)

  let is_eof : bool parser =
    let open Let_syntax in
    let%bind tokens = get in
    return (Sequence.is_empty tokens)

  let put_back token =
    let%bind tokens = get in
    put (Sequence.shift_right tokens token)

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
  let run p ~tokens = run p ~state:tokens
  let matches_prefix p ~tokens = Result.is_ok (run p ~tokens |> Tuple2.get1)

  let matches_full p ~tokens =
    let result, tokens = run p ~tokens in
    Result.is_ok result && Sequence.is_empty tokens

  let matches p ~tokens ~(match_type : [< `Full | `Prefix ]) =
    match match_type with
    | `Full -> matches_full p ~tokens
    | `Prefix -> matches_prefix p ~tokens
end
