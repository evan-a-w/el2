open! Core
module Parser_comb = Comb.Make (Token)
open Parser_comb
open Parser_comb.Let_syntax

let symbol_p =
  match%bind next with
  | Token.Symbol s -> return s
  | got -> error [%message "Expected symbol" (got : Token.t)]

let rec get_identifier () : String.t parser =
  let%bind token = next in
  match token with
  | Symbol s when not (Lexer.is_operator s || Lexer.is_keyword s) -> return s
  | LParen ->
      let%bind inner = symbol_p <|> get_identifier () in
      let%bind () = eat_token RParen in
      return inner
  | got -> error [%message "Expected binding" (got : Token.t)]

let type_expr_p () : Types.Type_expr.t parser =
  let rec single = get_identifier () >>| Types.Type_expr.single
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
      let%bind type_expr = type_expr_p () in
      return (`Other (tag, type_expr))
    in
    let without_tag = return (`Other (tag, Types.Type_expr.single tag)) in
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
        | `Other (tag, type_expr) ->
            { acc with others = (tag, type_expr) :: acc.others })
  in
  return { tag with others = List.rev tag.others }

let tag_p : Ast.Tag.t parser = tag_list_p <|> type_tag_p

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

let binding_p : Ast.binding parser = parse_maybe_tagged (get_identifier ())

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
  | Some (l_bp, r_bp) -> return (Ast.Var (operator, None), lhs, l_bp, r_bp)
  | None -> error [%message "Expected infix operator" ~got:(operator : string)]

let rec parse_a_node () : Ast.node parser =
  first [ parse_atom; parse_a_in_paren () ]
  |> map_error ~f:(fun _ -> [%message "Failed to parse (a expr)"])

and parse_a () : Ast.t parser =
  let%bind node, tag = parse_maybe_tagged (parse_a_node ()) in
  return { Ast.node; tag }

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
  let%bind node, tag = parse_in_paren_maybe_typed parse_b_node in
  return Ast.({ node; tag } |> Wrapped)

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
    let var = Ast.Var (operator, None) in
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

let parse =
  let%bind program = many (parse_let ()) in
  let%bind tokens = get in
  match Sequence.next tokens with
  | None -> return program
  | Some (got, _) -> error [%message "Unexpected token" (got : Token.t)]

let print_type_expr ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run (type_expr_p ()) ~tokens in
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
  let ast, tokens = run parse_one ~tokens in
  let tokens = Sequence.to_list tokens in
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
         (App (App (Var (= ())) (App (App (Var (+ ())) (Int 1)) (Int 2)))
          (Int 3))))))
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
            (App (App (Var (= ())) (App (App (Var (+ ())) (Int 1)) (Int 2)))
             (Int 3))))
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
                ((node (App (App (Var (+ ())) (Var (x ()))) (Var (y ())))))))))))
          ((node (Var (nested ())))))))))
     (tokens ())) |}]

let%expect_test "test_let_nested2" =
  let program = {|
    let x = 1 in let y = 2 in x + y
  |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (Let (x ()) ((node (Int 1)))
          ((node
            (Let (y ()) ((node (Int 2)))
             ((node (App (App (Var (+ ())) (Var (x ()))) (Var (y ())))))))))))))
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
  let ast, _ = run parse ~tokens in
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
              ((node (App (App (Var (+ ())) (Var (x ()))) (Var (y ()))))))))))))
       ((function2 ()) ((node (Lambda (x ()) ((node (Int 1)))))))
       ((function3 ())
        ((node
          (Lambda (x ())
           ((node
             (Lambda (y ())
              ((node
                (App (App (Var (+ ())) (App (Var (f ())) (Var (x ()))))
                 (Var (y ()))))))))))))
       ((if_ ())
        ((node (If ((node (Bool true))) ((node (Int 1))) ((node (Int 2)))))))
       ((if_nested ())
        ((node
          (If
           ((node
             (App (App (Var (= ())) (App (App (Var (+ ())) (Int 1)) (Int 2)))
              (Int 3))))
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
    {| ((ast (Ok ((tag ((type_expr (Single int)))) (node (Int 1))))) (tokens ())) |}]

let%expect_test "test_lots_type_tags" =
  let program =
    {|
    let (int : int) = (1 : int t)

    let nested = ((let x = 1 in let y = 2 in x + y) : (a, b, c) int t)

    let function2 = fun (x : string) -> (1 : int) |}
  in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect
    {|
    (ast
     (Ok
      (((int (((type_expr (Single int)))))
        ((tag ((type_expr (Multi ((Single int)) (Single t))))) (node (Int 1))))
       ((nested ())
        ((tag
          ((type_expr
            (Multi ((Single a) (Single b) (Single c))
             (Multi ((Single int)) (Single t))))))
         (node
          (Wrapped
           ((node
             (Let (x ()) ((node (Int 1)))
              ((node
                (Let (y ()) ((node (Int 2)))
                 ((node (App (App (Var (+ ())) (Var (x ()))) (Var (y ())))))))))))))))
       ((function2 ())
        ((node
          (Lambda (x (((type_expr (Single string)))))
           ((tag ((type_expr (Single int)))) (node (Int 1)))))))))) |}]

let%expect_test "test_apply_tags" =
  let program = {| g (1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (g ()))
          (Wrapped ((tag ((type_expr (Single int)))) (node (Int 1)))))))))
     (tokens ())) |}]

let%expect_test "test_apply_b" =
  let program = {| g (if 1 then 1 else 1 : int) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (g ()))
          (Wrapped
           ((tag ((type_expr (Single int))))
            (node (If ((node (Int 1))) ((node (Int 1))) ((node (Int 1))))))))))))
     (tokens ())) |}]

let%expect_test "test_nested_typed_application" =
  let program = {| g (f (1 : int) (a b (c d : int) : int)) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (Var (g ()))
          (Wrapped
           ((node
             (App
              (App (Var (f ()))
               (Wrapped ((tag ((type_expr (Single int)))) (node (Int 1)))))
              (Wrapped
               ((tag ((type_expr (Single int))))
                (node
                 (App (App (Var (a ())) (Var (b ())))
                  (Wrapped
                   ((tag ((type_expr (Single int))))
                    (node (App (Var (c ())) (Var (d ())))))))))))))))))))
     (tokens ())) |}]

let%expect_test "test_unary_bang" =
  let program = {| 1 + !2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok ((node (App (App (Var (+ ())) (Int 1)) (App (Var (! ())) (Int 2)))))))
     (tokens ())) |}]

let%expect_test "test_apply_left_assoc" =
  let program = {| f x y |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Ok ((node (App (App (Var (f ())) (Var (x ()))) (Var (y ())))))))
     (tokens ())) |}]

let%expect_test "test_operator_binding" =
  let program = {|
    let (+) = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect {| (ast (Ok (((+ ()) ((node (Int 1))))))) |}]

let%expect_test "test_operator_binding_fail" =
  let program = {|
    let + = 1
    |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse ~tokens in
  print_s
    [%message (ast : ((Ast.binding, Ast.t) Tuple2.t List.t, Sexp.t) Result.t)];
  [%expect {| (ast (Error ("Unexpected token" (got (Keyword let))))) |}]

let print_binding ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run binding_p ~tokens in
  print_s [%message (ast : (Ast.binding, Sexp.t) Result.t)]

let%expect_test "bindings" =
  print_binding ~program:"var";
  [%expect {| (ast (Ok (var ()))) |}];
  print_binding ~program:"(+)";
  [%expect {| (ast (Ok (+ ()))) |}];
  print_binding ~program:"+";
  [%expect {| (ast (Error ("Expected binding" (got (Symbol +))))) |}]

let%expect_test "test_wrapped_addition" =
  let program = {| (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok ((node (Wrapped ((node (App (App (Var (+ ())) (Int 4)) (Int 5)))))))))
     (tokens ())) |}]

let%expect_test "test_addition_and_times_binding" =
  let program = {| 1 * 2 + 3 * (4 + 5) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok
       ((node
         (App (App (Var (+ ())) (App (App (Var (* ())) (Int 1)) (Int 2)))
          (App (App (Var (* ())) (Int 3))
           (Wrapped ((node (App (App (Var (+ ())) (Int 4)) (Int 5)))))))))))
     (tokens ())) |}]

let print ~parser ~program =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parser ~tokens in
  print_s [%message (ast : (Ast.node, Sexp.t) Result.t)]

let%expect_test "super_simple_apply" =
  let program = {| f 1 |} in
  print ~parser:(parse_pratt ()) ~program;
  [%expect {| (ast (Ok (App (Var (f ())) (Int 1)))) |}]

let%expect_test "simple_apply" =
  let program = {| (f 1) |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast (Ok ((node (Wrapped ((node (App (Var (f ())) (Int 1)))))))))
     (tokens ())) |}]

let%expect_test "simple_prefix_apply" =
  let program = {| -f |} in
  test_parse_one ~program;
  [%expect
    {| ((ast (Ok ((node (App (Var (- ())) (Var (f ()))))))) (tokens ())) |}]

let%expect_test "simple_apply2" =
  let program = {| f 1 + 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok ((node (App (App (Var (+ ())) (App (Var (f ())) (Int 1))) (Int 2))))))
     (tokens ())) |}]

let%expect_test "simple_apply3" =
  let program = {| f 1 - 2 |} in
  test_parse_one ~program;
  [%expect
    {|
    ((ast
      (Ok ((node (App (App (Var (- ())) (App (Var (f ())) (Int 1))) (Int 2))))))
     (tokens ())) |}]

let%expect_test "test_tag_p" =
  let program = {| @[type : int, mode : local, name : "x"] |} in
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run tag_p ~tokens in
  print_s [%message (ast : (Ast.Tag.t, Sexp.t) Result.t)]

let%expect_test "test_tags" =
  let program = {| (f @[type : int, mode : local, name : "x"]) |} in
  test_parse_one ~program
