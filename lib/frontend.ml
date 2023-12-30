open! Core
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

let rec do_stuff ~f filename () =
  let dir, filename = Filename.split filename in
  Core_unix.chdir dir;
  let buf = Buffer.create 1024 in
  let seen_files = String.Hash_set.create () in
  on_file ~seen_files buf filename;
  let string = Buffer.contents buf in
  let lexbuf = Lexing.from_string string in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_do ~f lexbuf

and on_file ~seen_files buf filename =
  In_channel.with_file filename ~f:(fun inx ->
    In_channel.iter_lines inx ~f:(fun s ->
      let rex = Re.Pcre.regexp {|\$([a-zA-Z][a-zA-Z0-9]*)\((.*)\)|} in
      try
        let group = Re.Pcre.exec ~rex s in
        match Re.Group.get group 1 with
        | "include" ->
          let filename = Re.Group.get group 2 in
          (match Hash_set.mem seen_files filename with
           | true -> ()
           | false ->
             Hash_set.add seen_files filename;
             on_file ~seen_files buf filename)
        | _ -> failwith [%string {| unknown directive: %{s} |}]
      with
      | (Not_found [@warning "-3"]) ->
        Buffer.add_string buf s;
        Buffer.add_char buf '\n'))
;;

let print_ast ast =
  List.iter ast ~f:(fun toplevel ->
    print_endline @@ Sexp.to_string_hum @@ Ast.sexp_of_toplevel toplevel)
;;
