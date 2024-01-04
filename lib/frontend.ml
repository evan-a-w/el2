open! Core
open Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf
    outx
    "%s:%d:%d in lexeme %s\n"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)
    Lexing.(lexeme lexbuf)
;;

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | Syntax_error msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    []
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
;;

let parse_and_do ~f ~filename lexbuf =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let v = parse_with_error lexbuf in
  f v
;;

let do_stuff ~f filename =
  In_channel.with_file filename ~f:(fun chan ->
    let lexbuf = Lexing.from_channel chan in
    parse_and_do ~f ~filename lexbuf)
;;

let print_ast filename =
  do_stuff filename ~f:(fun ast ->
    List.iter ast ~f:(fun toplevel ->
      print_endline @@ Sexp.to_string_hum @@ Ast.sexp_of_toplevel toplevel))
;;
