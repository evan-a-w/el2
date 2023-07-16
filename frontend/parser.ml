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

let variance_p : Ast.Variance.t parser =
  eat_token (Token.Symbol "+")
  >>| (fun () -> Ast.Variance.Covariant)
  <|> (eat_token (Token.Symbol "-") >>| fun () -> Ast.Variance.Contravariant)
  <|> return Ast.Variance.Invariant

let rec type_binding_arg_p () : Ast.Type_binding.arg parser =
  let single =
    let%bind variance = variance_p in
    let%map name = lowercase_p in
    Ast.Type_binding.single (variance, name)
  in
  let tuple () = tuple_p type_binding_arg_p >>| Ast.Type_binding.tuple in
  tuple () <|> single

let type_binding_p () : Ast.Type_binding.t parser =
  let mono = lowercase_p >>| Ast.Type_binding.mono in
  let poly =
    let%bind arg = type_binding_arg_p () in
    let%map name = lowercase_p in
    Ast.Type_binding.poly (arg, name)
  in
  poly <|> mono

let type_expr_p () : Ast.Type_expr.t parser =
  let rec paren () =
    let%bind () = eat_token LParen in
    let%bind res = whole () in
    let%bind () = eat_token RParen in
    return res
  and a () = single_type_expr_p <|> paren () <|> pointer ()
  and pointer () =
    let%bind () = eat_token (Token.Symbol "&") in
    let%bind inner = a () in
    return (Ast.Type_expr.Pointer inner)
  and tuple () = qualified_p (tuple_p whole) >>| Ast.Type_expr.tuple
  and multi () =
    let%bind first = a () <|> tuple () in
    let%bind next = whole () in
    return (Ast.Type_expr.Multi (first, next))
  and whole () = multi () <|> a () <|> tuple () <|> pointer () in
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

let ast_tags_p : Ast.Ast_tags.t parser =
  let%bind () = eat_token Token.At in
  let%bind list =
    let%bind () = eat_token Token.LBrack in
    let%bind res = many_sep ast_tag_p ~sep:(eat_token Token.Comma) in
    let%map () = eat_token Token.RBrack in
    res
  in
  let tag =
    List.fold list ~init:Ast.Ast_tags.empty ~f:(fun acc (key, data) ->
        Ast.Tag.Map.change acc key ~f:(fun _ -> Some data))
  in
  return tag

let tag_list_p : Ast.Value_tag.t parser =
  let%bind () = eat_token Token.At in
  let inner_type_p =
    let%bind () = eat_token (Token.Keyword "type") in
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
    let%bind () = eat_token (Token.Keyword "mode") in
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
  let%bind second = tag_p in
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

let single_name_t (name : Ast.Lowercase.t) : Ast.expr =
  Ast.Node (Ast.Var (Ast.Qualified.Unqualified name))

let binding_power ~operator =
  match Pratt.infix_binding_power ~operator with
  | Some (l_bp, r_bp) -> return (l_bp, r_bp)
  | None -> error [%message "Expected infix operator" ~got:(operator : string)]

let rec parse_node () : Ast.node parser =
  first
    [ parse_atom; parse_wrapped_node (); parse_expruple (); parse_record () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_expruple () : Ast.node parser =
  qualified_p (tuple_p parse_expr) >>| fun x -> Ast.Tuple x

and parse_record () : Ast.node parser =
  qualified_p (record_p parse_expr) >>| fun x -> Ast.Record x

and parse_expr_no_type () : Ast.expr parser =
  first
    [
      parse_lambda ();
      parse_let_in ();
      parse_if ();
      parse_match ();
      parse_pratt ();
    ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (b expr)"])

and parse_expr () : Ast.expr parser =
  let%bind t = parse_expr_no_type () in
  let%map tag = optional tag_p in
  match tag with None -> t | Some tag -> Ast.Typed (t, tag)

and parse_wrapped_node () : Ast.node parser =
  let in_paren =
    let%bind () = eat_token LParen in
    let%bind inner = parse_expr () in
    let%map () = eat_token RParen in
    inner
  in
  let%map qualified = qualified_p in_paren in
  Ast.Wrapped qualified

and parse_lambda () : Ast.expr parser =
  let%bind () = eat_token (Token.Keyword "fun") <|> eat_token Token.Backslash in
  let%bind bindings = many_rev1 (binding_p ()) in
  let%bind () = eat_token Arrow in
  let%bind expr = parse_expr () in
  match bindings with
  | [] -> assert false
  | x :: xs ->
      let init = Ast.Lambda (x, expr) in
      let lambda = List.fold xs ~init ~f:(fun acc x -> Ast.Lambda (x, acc)) in
      return lambda

and parse_let () : (Ast.Binding.t * Ast.expr) parser =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind binding = binding_p () in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr = parse_expr () in
  return (binding, expr)

and parse_let_in () : Ast.expr parser =
  let%bind var, expr = parse_let () in
  let%bind () = eat_token (Token.Keyword "in") in
  let%bind body = parse_expr () in
  return (Ast.Let_in (var, expr, body))

and parse_if () : Ast.expr parser =
  let%bind () = eat_token (Token.Keyword "if") in
  let%bind cond = parse_expr () in
  let%bind () = eat_token (Token.Keyword "then") in
  let%bind then_ = parse_expr () in
  let%bind () = eat_token (Token.Keyword "else") in
  let%bind else_ = parse_expr () in
  return (Ast.If (cond, then_, else_))

and parse_match () : Ast.expr parser =
  let%bind () = eat_token (Token.Keyword "match") in
  let%bind first = parse_expr () in
  let%bind () = eat_token (Token.Keyword "with") in
  let one =
    let%bind binding = binding_p () in
    let%bind () = eat_token Token.Arrow in
    let%bind expr = parse_expr () in
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
  let constructor =
    let%bind name = constructor_name_p in
    match%bind get >>| Sequence.next with
    | Some (Token.Dot, _) -> error [%message "Unexpected dot"]
    | _ -> return (Ast.Constructor name)
  in
  let var = qualified_p (identifier_p ()) >>| fun x -> Ast.Var x in
  literal <|> var <|> constructor

and parse_op () : string parser =
  match%bind next with
  | Token.Symbol s when Lexer.is_operator s -> return s
  | got -> error [%message "Expected operator" (got : Token.t)]

and parse_node_with_prefix ?(min_bp = 0) () : Ast.expr parser =
  let prefixed =
    let%bind operator = parse_op () in
    let var = single_name_t operator in
    let%bind _ =
      match Pratt.prefix_binding_power ~operator with
      | Some bp when bp >= min_bp -> return bp
      | Some _ -> error [%message "Expected higher binding power"]
      | None ->
          error [%message "Expected prefix operator" ~got:(operator : string)]
    in
    let%bind rhs = parse_node () in
    return (Ast.App (var, Ast.Node rhs))
  in
  prefixed <|> (parse_node () >>| fun x -> Ast.Node x)

and parse_function_call () : Ast.expr parser =
  match%map
    many1
      (parse_node_with_prefix
         ~min_bp:(Pratt.infix_function_binding_power ())
         ())
  with
  | [] -> assert false
  | init :: rest -> List.fold_left rest ~init ~f:(fun acc x -> Ast.App (acc, x))

and parse_function_call_or_unary_prefix () =
  parse_function_call () <|> parse_node_with_prefix ()

and parse_pratt ?(min_bp = 0) () : Ast.expr parser =
  let%bind lhs = parse_function_call_or_unary_prefix () in
  let rec inner lhs =
    let%bind prev_state = get in
    match%bind optional (parse_op ()) with
    | None -> return lhs
    | Some operator ->
        let%bind l_bp, r_bp = binding_power ~operator in
        if l_bp < min_bp then
          let%bind () = put prev_state in
          return lhs
        else
          let%bind rhs = parse_pratt ~min_bp:r_bp () in
          inner (Ast.App (Ast.App (single_name_t operator, lhs), rhs))
  in
  inner lhs

and let_def_p () : Ast.let_def parser =
  parse_let () >>| fun (binding, expr) -> Ast.{ binding; expr }

and struct_p () : Ast.toplevel list parser =
  let%bind () = eat_token (Token.Keyword "struct") in
  let%bind res = parse_t () in
  let%map () = eat_token (Token.Keyword "end") in
  res

and module_def_struct_p () : Ast.module_def parser =
  let%map struct_ = struct_p () in
  Ast.Struct struct_

and module_def_named_p =
  let%map name = qualified_p uppercase_p in
  Ast.Named name

and module_def_typed_p () =
  let%bind () = eat_token Token.LParen in
  let%bind def = module_def_p () in
  let%bind () = eat_token Token.Colon in
  let%bind signature = module_sig_p () in
  let%map () = eat_token Token.RParen in
  Ast.Module_typed (def, signature)

and module_def_in_paren_p () =
  let%bind () = eat_token Token.LParen in
  let%bind def = module_def_p () in
  let%map () = eat_token Token.RParen in
  def

and module_def_no_functor_p () =
  module_def_named_p <|> module_def_struct_p () <|> module_def_in_paren_p ()
  <|> module_def_typed_p ()

and module_def_functor_app_p () =
  let%bind first = module_def_no_functor_p () in
  let%map args = many1 (module_def_typed_p () <|> module_def_in_paren_p ()) in
  Ast.Functor_app (first, args)

and module_def_p () = module_def_functor_app_p () <|> module_def_no_functor_p ()

and module_def_arg_p () : (Ast.Uppercase.t * Ast.module_sig) parser =
  let%bind () = eat_token Token.LParen in
  let%bind name = uppercase_p in
  let%bind () = eat_token Token.Colon in
  let%bind sig_ = module_sig_p () in
  let%map () = eat_token Token.RParen in
  (name, sig_)

and module_description_p ?(optional_sig_fn = optional) () =
  let%bind () = eat_token (Token.Keyword "module") in
  let%bind name = uppercase_p in
  let%bind args = many (module_def_arg_p ()) in
  let with_sig =
    let%bind () = eat_token Token.Colon in
    module_sig_p ()
  in
  let%map maybe_sig = optional_sig_fn with_sig in
  (name, args, maybe_sig)

and module_sig_binding_p () =
  let%bind () = eat_token (Token.Keyword "let") in
  let%bind binding = binding_p () in
  let%map tag = tag_p in
  Ast.Sig_binding (binding, tag)

and module_sig_type_def_p () =
  let no_def =
    let%bind () = eat_token (Token.Keyword "type") in
    let%bind type_name = type_binding_p () in
    let%map ast_tags =
      optional ast_tags_p >>| Option.value ~default:Ast.Ast_tags.empty
    in
    Ast.Sig_type_def { type_name; type_def = None; ast_tags }
  in
  let with_def =
    let%map type_name, type_def, ast_tags = typedef_p () in
    Ast.Sig_type_def { type_name; type_def = Some type_def; ast_tags }
  in
  no_def <|> with_def

and module_sig_module_p () =
  let%map module_name, functor_args, module_sig =
    module_description_p
      ~optional_sig_fn:(fun x ->
        let%map res = x in
        Some res)
      ()
  in
  match module_sig with
  | None -> assert false
  | Some module_sig -> Ast.Sig_module { module_name; functor_args; module_sig }

and module_sig_p () : Ast.module_sig parser =
  let%bind () = eat_token (Token.Keyword "sig") in
  let each =
    module_sig_binding_p () <|> module_sig_type_def_p ()
    <|> module_sig_module_p ()
  in
  let%bind res = many each in
  let%map () = eat_token (Token.Keyword "end") in
  res

and record_type_def_lit_p () =
  let%bind () = eat_token Token.LBrace in
  let each =
    let%bind mut =
      optional (eat_token (Token.Keyword "mutable")) >>| Option.is_some
    in
    let%bind name = lowercase_p in
    let%bind () = eat_token Token.Colon in
    let%bind type_expr = type_expr_p () in
    return (name, (type_expr, mut))
  in
  let%bind list = many_sep each ~sep:(eat_token Token.Semicolon) in
  let%bind _ = optional (eat_token Token.Semicolon) in
  let%map () = eat_token Token.RBrace in
  let record = Ast.Lowercase.Map.of_alist_exn list in
  Ast.Type_def_lit.Record record

and enum_type_def_lit_p () =
  let%bind _ = optional (eat_token Token.Pipe) in
  let each =
    let%bind constructor = uppercase_p in
    let%bind value_type = optional type_expr_no_spaces_p in
    return (constructor, value_type)
  in
  let%bind list = many_sep1 each ~sep:(eat_token Token.Pipe) in
  let map = Ast.Uppercase.Map.of_alist_exn list in
  return (Ast.Type_def_lit.Enum map)

and typedef_p () =
  let type_expr_lit_p = type_expr_p () >>| Ast.Type_def_lit.type_expr in
  let%bind () = eat_token (Token.Keyword "type") in
  let%bind name = type_binding_p () in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind expr =
    record_type_def_lit_p () <|> enum_type_def_lit_p () <|> type_expr_lit_p
  in
  let%map ast_tags =
    optional ast_tags_p >>| Option.value ~default:Ast.Ast_tags.empty
  in
  (name, expr, ast_tags)

and typedef_toplevel_p () : Ast.toplevel parser =
  let%map type_name, type_def, ast_tags = typedef_p () in
  Ast.Type_def { type_name; type_def; ast_tags }

and module_def_toplevel_p () : Ast.toplevel parser =
  let%bind module_name, functor_args, module_sig = module_description_p () in
  let module_description = Ast.{ module_name; functor_args; module_sig } in
  let%bind () = eat_token (Token.Symbol "=") in
  let%bind module_def = module_def_p () in
  return (Ast.Module_def { module_description; module_def })

and toplevel_p () : Ast.toplevel parser =
  let let_toplevel_p = let_def_p () >>| fun x -> Ast.Let x in
  let_toplevel_p <|> typedef_toplevel_p () <|> module_def_toplevel_p ()

and parse_t () : Ast.t parser = many (toplevel_p ())

let parse_one = parse_expr ()

let parse_t =
  let%bind res = parse_t () in
  match%bind get >>| Sequence.next with
  | None -> return res
  | Some (got, _) -> error [%message "Unexpected token" (got : Token.t)]
