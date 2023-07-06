open! Core
open Angstrom
open Angstrom.Let_syntax

let keywords = [ "let"; "in"; "match"; "with"; "then"; "else"; "if"; "fun" ]
let is_digit = function '0' .. '9' -> true | _ -> false
let int_p = take_while1 is_digit >>| Int.of_string >>| Token.int

let float_p =
  lift3
    (fun x y z -> float_of_string (x ^ y ^ z))
    (take_while1 is_digit) (string ".") (take_while is_digit)
  >>| Token.float

let string_p =
  let inside_string =
    (* for some reason one cant be recursive so use a ref *)
    let one =
      fix @@ fun one ->
      match%bind any_char with
      | '"' -> fail "should not terminate inside one"
      | '\\' -> (
          match%bind any_char with
          | '"' -> '"' |> return
          | '\\' -> '\\' |> return
          | 'n' -> '\n' |> return
          | 't' -> '\t' |> return
          | 'r' -> '\r' |> return
          | 'b' -> '\b' |> return
          | '\n' | '\t' | ' ' -> one
          | c -> return c)
      | c -> return c
    in
    let terminated =
      match%bind any_char with '"' -> return '"' | _ -> fail "unterminated"
    in
    Base.String.of_char_list <$> many_till one terminated
  in
  char '"' *> inside_string >>| Token.string

let bool_p =
  string "true" *> return true <|> string "false" *> return false >>| Token.bool

let arrow_p = string "->" *> return Token.Arrow

let symbol_p =
  let is_ident_start =
    let ident_extras = "!@#$%^&*-+_:<>?/=" in
    function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
    | x when String.mem ident_extras x -> true
    | _ -> false
  in

  let is_ident c = is_ident_start c || is_digit c || String.mem "'." c in
  let%bind first = satisfy is_ident_start in
  let%bind rest = take_while is_ident in
  let ident = String.concat [ String.of_char first; rest ] in
  match List.find keywords ~f:(String.equal ident) with
  | Some keyword -> return (Token.Keyword keyword)
  | None -> return (Token.Symbol ident)

let pipe_p = char '|' *> return Token.Pipe
let comma_p = char ',' *> return Token.Comma
let lparen_p = char '(' *> return Token.LParen
let rparen_p = char ')' *> return Token.RParen
let colon_p = char ':' *> return Token.Colon

let whitespace_p =
  skip_while (function ' ' | '\n' | '\t' -> true | _ -> false)

let parser =
  let%bind () = whitespace_p in
  let%bind token =
    colon_p <|> float_p <|> int_p <|> string_p <|> bool_p <|> arrow_p
    <|> symbol_p <|> pipe_p <|> comma_p <|> lparen_p <|> rparen_p
  in
  let%bind () = whitespace_p in
  return token

let lex ~program = Angstrom.parse_string ~consume:All (many1 parser) program

let%expect_test "lex" =
  let program =
    "let x = 1 in x -> hi w.eqwe'eq 3,1231230 12.3123 penis match | ,"
  in
  let lexed = lex ~program in
  print_s [%sexp (lexed : (Token.t List.t, String.t) Result.t)];
  [%expect
    {|
    (Ok
     ((Keyword let) (Symbol x) (Symbol =) (Int 1) (Keyword in) (Symbol x) Arrow
      (Symbol hi) (Symbol w.eqwe'eq) (Int 3) Comma (Int 1231230) (Float 12.3123)
      (Symbol penis) (Keyword match) Pipe Comma)) |}]
