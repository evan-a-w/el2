open Core
open El2
open Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf
    outx
    "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)
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

let parse_and_do ~f lexbuf =
  let v = parse_with_error lexbuf in
  f v
;;

let loop ~f filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_do ~f lexbuf;
  In_channel.close inx
;;

let print_ast ast =
  List.iter ast ~f:(fun toplevel ->
    print_endline @@ Sexp.to_string_hum @@ Ast.sexp_of_toplevel toplevel)
;;

let make_cmd ~summary ~f =
  Command.basic_spec
    ~summary
    Command.Spec.(empty +> anon ("filename" %: string))
    (loop ~f)
;;

let () =
  Command.group
    ~summary:"Operate on evanlang2 files"
    [ "--parse", make_cmd ~summary:"Parse evanlang2" ~f:print_ast
    ; ( "--dump-type-state"
      , make_cmd ~summary:"Do some stuff" ~f:Type_check.process_and_dump )
    ; ( "--typed-ast"
      , make_cmd ~summary:"print out the typed ast" ~f:Backend.print_typed_ast )
    ; "--compile", make_cmd ~summary:"compile" ~f:Backend.compile_fully
    ]
  |> Command_unix.run
;;
