open! Core
module Parser_comb = Comb.Make (Token)
open Parser_comb
open Parser_comb.Let_syntax

let symbol_p =
  match%bind next with
  | Token.Symbol s -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

let parse_in_paren p =
  let%bind () = eat_token LParen in
  let%bind inner = p in
  let%bind () = eat_token RParen in
  return inner

let maybe_in_paren p = parse_in_paren p <|> p

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
  | Symbol s
    when not
           (Lexer.is_operator s || Lexer.is_keyword s || Char.is_uppercase s.[0])
    ->
      return s
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

let literal_p : Ast.Literal.t parser =
  match%bind next with
  | Token.Int x -> Ast.Literal.Int x |> return
  | Float f -> Ast.Literal.Float f |> return
  | Bool b -> Ast.Literal.Bool b |> return
  | String s -> Ast.Literal.String s |> return
  | LParen ->
      let%bind () = eat_token RParen in
      return Ast.Literal.Unit
  | got -> error [%message "Expected atom" (got : Token.t)]

let constructor_name_p = qualified_p (maybe_in_paren uppercase_p)

let tuple_p p : 'a Ast.Tuple.t parser =
  let%bind () = eat_token Token.LParen in
  let%bind res = many_sep2 (p ()) ~sep:(eat_token Token.Comma) in
  let%map () = eat_token Token.RParen in
  res

let single_type_expr_p = qualified_p (identifier_p ()) >>| Ast.Type_expr.single

let type_expr_p () : Ast.Type_expr.t parser =
  let rec paren () =
    let%bind () = eat_token LParen in
    let%bind res = whole () in
    let%bind () = eat_token RParen in
    return res
  and a () = single_type_expr_p <|> paren ()
  and tuple () = qualified_p (tuple_p whole) >>| Ast.Type_expr.tuple
  and multi () =
    let%bind first = a () <|> tuple () in
    let%bind next = whole () in
    return (Ast.Type_expr.Multi (first, next))
  and whole () = multi () <|> a () <|> tuple () in
  whole ()

let type_expr_no_spaces_p =
  parse_in_paren (type_expr_p ())
  <|> single_type_expr_p
  <|> (qualified_p (tuple_p type_expr_p) >>| Ast.Type_expr.tuple)

let ast_tag_p : (Ast.Tag.t * Token.t list) parser =
  let%bind tag = symbol_p in
  let with_tag =
    let%bind () = eat_token Token.Colon in
    let accepted_token token =
      not (List.exists ~f:(Token.equal token) [ Token.Comma; Token.RBrack ])
    in
    let%bind list = many1 (satisfies accepted_token) in
    return (tag, list)
  in
  let without_tag = return (tag, []) in
  with_tag <|> without_tag

let type_tag_p =
  let%bind () = eat_token Token.Colon in
  let%bind type_expr_ = type_expr_p () in
  return { Ast.Value_tag.empty with type_expr = Some type_expr_ }

let tag_list_p : Ast.Value_tag.t parser =
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
    let%bind res = ast_tag_p in
    return (`Other res)
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
    List.fold list ~init:Ast.Value_tag.empty ~f:(fun acc x ->
        match x with
        | `Type_expr type_expr -> { acc with type_expr = Some type_expr }
        | `Mode mode -> { acc with mode = Some mode }
        | `Other (key, data) ->
            { acc with ast_tags = Ast.Tag.Map.add_exn acc.ast_tags ~key ~data })
  in
  return tag

let tag_p : Ast.Value_tag.t parser =
  let%bind type_tag = optional type_tag_p in
  let%bind tag_list = optional tag_list_p in
  match (type_tag, tag_list) with
  | Some type_tag, Some tag_list ->
      return Ast.Value_tag.{ tag_list with type_expr = type_tag.type_expr }
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

let record_p ?(from_name = Fn.const None) p : 'a Ast.Lowercase.Map.t parser =
  let%bind () = eat_token Token.LBrace in
  let each =
    let%bind name = lowercase_p in
    let%bind value =
      if_ (eat_token Token.Colon)
        ~then_:(p () >>| Option.some)
        ~else_:(return (from_name name))
    in
    match value with
    | None -> error [%message "Expected value"]
    | Some value -> return (name, value)
  in
  let%bind list = many_sep each ~sep:(eat_token Token.Semicolon) in
  let%bind _ = optional (eat_token Token.Semicolon) in
  let%map () = eat_token Token.RBrace in
  Ast.Lowercase.Map.of_alist_exn list

let name_binding_p : Ast.Binding.t parser =
  let%map name = identifier_p () in
  Ast.Binding.Name name

let literal_binding_p : Ast.Binding.t parser =
  let%map literal = literal_p in
  Ast.Binding.Literal literal

let rec binding_p () : Ast.Binding.t parser =
  first
    [
      constructor_binding_p ();
      tuple_binding_p ();
      record_binding_p ();
      renamed_binding_p ();
      typed_binding_p ();
      name_binding_p;
      literal_binding_p;
    ]
  |> map_error ~f:(fun _ -> [%message "Expected binding"])

and renamed_binding_p () =
  let%bind () = eat_token Token.LParen in
  let%bind first = binding_p () in
  let%bind () = eat_token (Token.Keyword "as") in
  let%bind second = identifier_p () in
  let res = Ast.Binding.Renamed (first, second) in
  let%map () = eat_token Token.RParen in
  res

and typed_binding_p () =
  let%bind () = eat_token Token.LParen in
  let%bind first = binding_p () in
  let%bind second = type_tag_p in
  let res = Ast.Binding.Typed (first, second) in
  let%map () = eat_token Token.RParen in
  res

and constructor_binding_p () =
  let%bind name = constructor_name_p in
  let%map inner = optional (maybe_in_paren (binding_p ())) in
  Ast.Binding.Constructor (name, inner)

and tuple_binding_p () =
  let%map tuple =
    (fun () -> maybe_in_paren (binding_p ())) |> tuple_p |> qualified_p
  in
  Ast.Binding.Tuple tuple

and record_binding_p () =
  let inner =
    record_p ~from_name:(Fn.compose Option.some Ast.Binding.name) binding_p
  in
  qualified_p inner >>| Ast.Binding.record

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

let single_name_t name =
  Ast.Node (Ast.Var (Ast.Qualified.Unqualified (Ast.Binding.name name)))

let binding_power ~lhs ~operator : (Ast.t * Ast.t * int * int) parser =
  match Pratt.infix_binding_power ~operator with
  | Some (l_bp, r_bp) -> return (single_name_t operator, lhs, l_bp, r_bp)
  | None -> error [%message "Expected infix operator" ~got:(operator : string)]

let rec parse_node () : Ast.node parser =
  first [ parse_atom; parse_wrapped_node (); parse_tuple () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_tuple () : Ast.node parser =
  qualified_p (tuple_p parse_t) >>| fun x -> Ast.Tuple x

and parse_t_no_type () : Ast.t parser =
  first
    [
      parse_lambda ();
      parse_let_in ();
      parse_if ();
      parse_match ();
      parse_apply ();
      parse_pratt ();
      (parse_node () >>| fun x -> Ast.Node x);
    ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])

and parse_t () : Ast.t parser =
  let%bind t = parse_t_no_type () in
  let%map tag = optional type_tag_p in
  match tag with None -> t | Some tag -> Ast.Typed (t, tag)

and parse_wrapped_node () : Ast.node parser =
  let in_paren =
    let%bind () = eat_token LParen in
    let%bind inner = parse_t () in
    let%map () = eat_token RParen in
    inner
  in
  let%map qualified = qualified_p in_paren in
  Ast.Wrapped qualified

and parse_lambda () : Ast.t parser =
  let%bind () = eat_token (Token.Keyword "fun") <|> eat_token Token.Backslash in
  let%bind bindings = many_rev1 (binding_p ()) in
  let%bind () = eat_token Arrow in
  let%bind expr = parse_t () in
  match bindings with
  | [] -> assert false
  | x :: xs ->
      let init = Ast.Lambda (x, expr) in
      let lambda = List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (x, acc)) in
      return lambda

and parse_let () : (Ast.Binding.t * Ast.t) parser =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind binding = binding_p () in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse_t () in
  return (binding, expr)

and parse_let_in () : Ast.t parser =
  let%bind var, expr = parse_let () in
  let%bind () = eat_token (Token.Keyword "in") in
  let%bind body = parse_t () in
  return (Ast.Let (var, expr, body))

and parse_if () : Ast.t parser =
  let%bind () = eat_token (Token.Keyword "if") in
  let%bind cond = parse_t () in
  let%bind () = eat_token (Token.Keyword "then") in
  let%bind then_ = parse_t () in
  let%bind () = eat_token (Token.Keyword "else") in
  let%bind else_ = parse_t () in
  return (Ast.If (cond, then_, else_))

and parse_match () : Ast.t parser =
  let%bind () = eat_token (Token.Keyword "match") in
  let%bind first = parse_t () in
  let%bind () = eat_token (Token.Keyword "with") in
  let one =
    let%bind binding = binding_p () in
    let%bind () = eat_token Token.Arrow in
    let%bind expr = parse_t () in
    return (binding, expr)
  in
  let%bind _ = optional (eat_token Token.Pipe) in
  let%bind rest = many_sep1 one ~sep:(eat_token Token.Pipe) in
  return (Ast.Match (first, rest))

and parse_atom : Ast.node parser =
  let literal =
    let%map literal = literal_p in
    Ast.Literal literal
  in
  let binding = qualified_p name_binding_p >>| fun x -> Ast.Var x in
  literal <|> binding

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
    let%map a = parse_node () in
    `A a
  in
  op <|> a

and parse_a_with_prefix ?(min_bp = 0) () : Ast.t parser =
  let prefixed =
    let%bind operator = parse_op () in
    let var =
      Ast.Node (Ast.Var (Ast.Qualified.Unqualified (Ast.Binding.name operator)))
    in
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
  prefixed <|> (parse_node () >>| fun x -> Ast.Node x)

and parse_pratt ?(min_bp = 0) ?lhs () : Ast.t parser =
  let%bind lhs =
    match lhs with
    | Some lhs -> return lhs
    | None -> parse_a_with_prefix ~min_bp ()
  in
  let rec inner (lhs : Ast.t) =
    let get_more =
      let%bind prev_state = get in
      let%bind op_or_a = parse_op_or_a () in
      let%bind op, lhs, l_bp, r_bp =
        match op_or_a with
        | `A a ->
            let bp = Pratt.infix_function_binding_power () in
            return (lhs, Ast.Node a, bp, bp + 1)
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

and parse_apply () : Ast.t parser =
  let%bind first = parse_pratt () in
  let%bind operator = parse_op () in
  let%bind operator, _, _, r_bp = binding_power ~operator ~lhs:first in
  let%bind second =
    parse_pratt ~min_bp:r_bp () <|> (parse_node () >>| fun x -> Ast.Node x)
  in
  return (Ast.App (Ast.App (operator, first), second))

let parse_one : Ast.t parser = parse_t ()

let record_type_def_lit_p =
  let%map record = record_p type_expr_p in
  Ast.Type_def_lit.Record record

let enum_type_def_lit_p =
  let%bind _ = optional (eat_token Token.Pipe) in
  let each =
    let%bind constructor = uppercase_p in
    let%bind value_type = optional type_expr_no_spaces_p in
    return (constructor, value_type)
  in
  let%bind list = many_sep1 each ~sep:(eat_token Token.Pipe) in
  let map = Ast.Uppercase.Map.of_alist_exn list in
  return (Ast.Type_def_lit.Enum map)

let typedef_toplevel_p : Ast.Toplevel.t parser =
  let type_expr_lit_p = type_expr_p () >>| Ast.Type_def_lit.type_expr in
  let%bind () = eat_token (Token.Keyword "type") in
  let%bind name = type_expr_p () in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr =
    record_type_def_lit_p <|> enum_type_def_lit_p <|> type_expr_lit_p
  in
  return (Ast.Toplevel.Type_def { name; expr })

let parse_toplevel : Ast.Toplevel.t List.t parser =
  let let_toplevel_p =
    parse_let () >>| fun (binding, expr) -> Ast.Toplevel.Let { binding; expr }
  in
  let inner = let_toplevel_p <|> typedef_toplevel_p in
  let%bind program = many inner in
  let%bind tokens = get in
  match Sequence.next tokens with
  | None -> return program
  | Some (got, _) -> error [%message "Unexpected token" (got : Token.t)]
