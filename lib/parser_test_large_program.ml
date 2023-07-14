open! Core
open Parser.Parser_comb
open! Parser

let program =
  {|
   module X = struct
     let x = 1
     let y = 2

     type t = int string
   end
|}

let%expect_test "parse" =
  let tokens = Result.ok_or_failwith (Lexer.lex ~program) in
  let ast, _ = run parse_t ~tokens in
  print_s [%message (ast : (Ast.t, Sexp.t) Result.t)]
