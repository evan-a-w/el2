open! Core
module Parser_comb = Comb.Make (Token)
open Parser_comb
open Parser_comb.Let_syntax

let symbol_p =
  match%bind next with
  | Token.Symbol s -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

let lowercase_p =
  match%bind next with
  | Token.Symbol s when s.[0] |> Char.is_lowercase -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

let uppercase_p =
  match%bind next with
  | Token.Symbol s when s.[0] |> Char.is_uppercase -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

let rec identifier_p () : String.t parser =
  let%bind token = next in
  match token with
  | Symbol s when not (Lexer.is_operator s || Lexer.is_keyword s) -> return s
  | LParen ->
      let%bind inner = symbol_p <|> identifier_p () in
      let%bind () = eat_token RParen in
      return inner
  | got -> error [%message "Expected binding" (got : Token.t)]

let module_name_p = uppercase_p

let qualified_p p : 'a Ast.Qualified.t parser =
  let rec inner () =
    let indexed =
      let%bind name = module_name_p in
      let%bind () = eat_token Token.Dot in
      let%bind rest = inner () in
      return Ast.Qualified.(Qualified (name, rest))
    in
    let base =
      let%map res = p in
      Ast.Qualified.Unqualified res
    in
    indexed <|> base
  in
  inner ()

let tuple_p p : 'a Ast.Tuple.t parser =
  let%bind () = eat_token Token.LParen in
  let%bind res = many_sep2 (p ()) ~sep:(eat_token Token.Comma) in
  let%map () = eat_token Token.RParen in
  res

let type_expr_p () : Ast.Type_expr.t parser =
  let rec single = qualified_p (identifier_p ()) >>| Ast.Type_expr.single
  and paren () =
    let%bind () = eat_token LParen in
    let%bind res = whole () in
    let%bind () = eat_token RParen in
    return res
  and a () = single <|> paren ()
  and tuple () = qualified_p (tuple_p whole) >>| Ast.Type_expr.tuple
  and multi () =
    let%bind first = a () <|> tuple () in
    let%bind next = whole () in
    return (Ast.Type_expr.Multi (first, next))
  and whole () = multi () <|> a () <|> tuple () in
  whole ()

let type_tag_p =
  let%bind () = eat_token Token.Colon in
  let%bind type_expr_ = type_expr_p () in
  return Ast.Tag.{ type_expr = Some type_expr_; mode = None; others = [] }

let tag_list_p : Ast.Tag.t parser =
  let%bind () = eat_token Token.At in
  let inner_type_p =
    let%bind () = eat_token (Token.Symbol "type") in
    let%bind () = eat_token Token.Colon in
    let%bind res = type_expr_p () in
    return (`Type_expr res)
  in
  let allocation_p =
    eat_token (Token.Symbol "local")
    >>| Fn.const `Local
    <|> (eat_token (Token.Symbol "global") >>| Fn.const `Global)
    >>| Ast.Mode.allocation
  in
  let mode_p =
    let%bind () = eat_token (Token.Symbol "mode") in
    let%bind () = eat_token Token.Colon in
    let%bind res = allocation_p in
    return (`Mode res)
  in
  let other_p =
    let%bind tag = symbol_p in
    let with_tag =
      let%bind () = eat_token Token.Colon in
      let accepted_token token =
        not (List.exists ~f:(Token.equal token) [ Token.Comma; Token.RBrack ])
      in
      let%bind list = many1 (satisfies accepted_token) in
      return (`Other (tag, list))
    in
    let without_tag = return (`Other (tag, [])) in
    with_tag <|> without_tag
  in
  let%bind list =
    let%bind () = eat_token Token.LBrack in
    let%bind res =
      many_sep
        (first [ inner_type_p; mode_p; other_p ])
        ~sep:(eat_token Token.Comma)
    in
    let%map () = eat_token Token.RBrack in
    res
  in
  let tag =
    List.fold list ~init:Ast.Tag.empty ~f:(fun acc x ->
        match x with
        | `Type_expr type_expr -> { acc with type_expr = Some type_expr }
        | `Mode mode -> { acc with mode = Some mode }
        | `Other x -> { acc with others = x :: acc.others })
  in
  return { tag with others = List.rev tag.others }

let tag_p : Ast.Tag.t parser =
  let%bind type_tag = maybe type_tag_p in
  let%bind tag_list = maybe tag_list_p in
  match (type_tag, tag_list) with
  | Some type_tag, Some tag_list ->
      return Ast.Tag.{ tag_list with type_expr = type_tag.type_expr }
  | Some type_tag, None -> return type_tag
  | None, Some tag_list -> return tag_list
  | None, None -> error [%message "Expected tag"]

let parse_tagged p =
  let%bind () = eat_token LParen in
  let%bind inner = p in
  let%bind tag = tag_p in
  let%bind () = eat_token RParen in
  return (inner, tag)

let parse_maybe_tagged p =
  let fst =
    let%bind a, b = parse_tagged p in
    return (a, Some b)
  in
  let snd = p >>| fun x -> (x, None) in
  fst <|> snd

let binding_p : Ast.Binding.t parser = parse_maybe_tagged (identifier_p ())

let parse_in_paren p =
  let%bind () = eat_token LParen in
  let%bind inner = p in
  let%bind () = eat_token RParen in
  return inner

let[@inline] parse_in_paren_maybe_typed p =
  let%bind () = eat_token LParen in
  let%bind inner = p () in
  let without_type_tag =
    let%bind () = eat_token RParen in
    return None
  in
  let with_type_tag =
    let%bind tag = tag_p in
    let%bind () = eat_token RParen in
    return (Some tag)
  in
  let%bind tag = with_type_tag <|> without_type_tag in
  return (inner, tag)

let binding_power ~lhs ~operator =
  match Pratt.infix_binding_power ~operator with
  | Some (l_bp, r_bp) ->
      return
        (Ast.Var (Ast.Qualified.Unqualified (operator, None)), lhs, l_bp, r_bp)
  | None -> error [%message "Expected infix operator" ~got:(operator : string)]

let rec parse_a_node () : Ast.node parser =
  first [ parse_atom; parse_a_in_paren (); parse_tuple () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_a () : Ast.t parser =
  let%bind node, tag = parse_maybe_tagged (parse_a_node ()) in
  return { Ast.node; tag }

and parse_tuple () : Ast.node parser =
  qualified_p (tuple_p parse_b_node) >>| fun x -> Ast.Tuple x

and parse_b_node () : Ast.node parser =
  first
    [
      parse_lambda ();
      parse_let_in ();
      parse_if ();
      parse_apply ();
      parse_pratt ();
      parse_a_node ();
    ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])

and parse_b () : Ast.t parser =
  let%bind node, tag = parse_maybe_tagged (parse_b_node ()) in
  return { Ast.node; tag }

and parse_a_in_paren () : Ast.node parser =
  let in_paren =
    let%bind node, tag = parse_in_paren_maybe_typed parse_b_node in
    return Ast.{ node; tag }
  in
  let%map qualified = qualified_p in_paren in
  Ast.Wrapped qualified

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
        List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (x, Ast.untagged acc))
      in
      return lambda

and parse_let () : (Ast.Binding.t * Ast.t) parser =
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
  let binding = qualified_p binding_p >>| fun x -> Ast.Var x in
  non_binding <|> binding

and parse_op () : string parser =
  match%bind next with
  | Token.Symbol s when Lexer.is_operator s -> return s
  | got -> error [%message "Expected operator" (got : Token.t)]

and parse_op_or_a () =
  let op =
    let%map op = parse_op () in
    `Op op
  in
  let a =
    let%map a = parse_a_node () in
    `A a
  in
  op <|> a

and parse_a_with_prefix ?(min_bp = 0) () : Ast.node parser =
  let prefixed =
    let%bind operator = parse_op () in
    let var = Ast.Var (Ast.Qualified.Unqualified (operator, None)) in
    let%bind min_bp =
      match Pratt.prefix_binding_power ~operator with
      | Some bp when bp >= min_bp -> return bp
      | Some _ -> error [%message "Expected higher binding power"]
      | None ->
          error [%message "Expected prefix operator" ~got:(operator : string)]
    in
    let%bind rhs = parse_pratt ~min_bp () in
    return (Ast.App (var, rhs))
  in
  prefixed <|> parse_a_node ()

and parse_pratt ?(min_bp = 0) ?lhs () : Ast.node parser =
  let%bind lhs =
    match lhs with
    | Some lhs -> return lhs
    | None -> parse_a_with_prefix ~min_bp ()
  in
  let rec inner (lhs : Ast.node) =
    let get_more =
      let%bind prev_state = get in
      let%bind op_or_a = parse_op_or_a () in
      let%bind op, lhs, l_bp, r_bp =
        match op_or_a with
        | `A a ->
            let bp = Pratt.infix_function_binding_power () in
            return (lhs, a, bp, bp + 1)
        | `Op operator -> binding_power ~operator ~lhs
      in
      let curr = Ast.App (op, lhs) in
      let without_rhs =
        match op_or_a with `A _ -> return curr | `Op _ -> error [%message ""]
      in
      if l_bp < min_bp then
        let%bind () = put prev_state in
        return lhs
      else
        let with_rhs =
          let%bind rhs = parse_pratt ~min_bp:r_bp () in
          inner (Ast.App (curr, rhs))
        in
        with_rhs <|> without_rhs
    in
    get_more <|> return lhs
  in
  inner lhs

and parse_apply () : Ast.node parser =
  let%bind first = parse_pratt () in
  let%bind operator = parse_op () in
  let%bind operator, _, _, r_bp = binding_power ~operator ~lhs:first in
  let%bind second = parse_pratt ~min_bp:r_bp () <|> parse_a_node () in
  return (Ast.App (Ast.App (operator, first), second))

let parse_one = parse_b ()

let parse_toplevel : Ast.Toplevel.t List.t parser =
  let parse_let =
    parse_let () >>| fun (binding, expr) -> Ast.Toplevel.Let { binding; expr }
  in
  let inner = parse_let in
  let%bind program = many inner in
  let%bind tokens = get in
  match Sequence.next tokens with
  | None -> return program
  | Some (got, _) -> error [%message "Unexpected token" (got : Token.t)]
