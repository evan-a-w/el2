{
open Lexing
open Parser

exception Syntax_error of string

let nested_comment_count = ref 0
}

let int = '-'? ['0'-'9'] ['0'-'9']*

let digit = ['0'-'9']
let frac = '.' digit+
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

let dollar = '$'

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let upper_id = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white    { read lexbuf }
  | newline  { new_line lexbuf; read lexbuf }
  | "let"    { LET }
  | "type"   { TYPE }
  | "if"     { IF }
  | "then"   { THEN }
  | "loop"   { LOOP }
  | "break"  { BREAK }
  | "else"   { ELSE }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "null"   { NULL }
  | "return" { RETURN }
  | "sizeof" { SIZE_OF }
  | "assert" { ASSERT }
  | "match"  { MATCH }
  | "module" { MODULE }
  | "open"   { OPEN }
  | "open_file" { OPEN_FILE }
  | "with"   { WITH }
  | "unsafe_cast"   { UNSAFE_CAST }
  | "extern"   { EXTERN }
  | "implicit_extern"   { IMPLICIT_EXTERN }
  | id       { ID (Lexing.lexeme lexbuf) }
  | upper_id { UPPER_ID (Lexing.lexeme lexbuf) }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float    { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | "+"      { PLUS }
  | "-"      { MINUS }
  | "[*"     { incr nested_comment_count; in_comment lexbuf }
  | "*"      { TIMES }
  | "/"      { DIV }
  | "%"      { REM }
  | "#"      { HASH }
  | "."      { DOT }
  | "|"      { PIPE }
  | "("      { LPAREN }
  | ")"      { RPAREN }
  | "{|"     { LBRACEPIPE }
  | "|}"     { PIPERBRACE }
  | "{"      { LBRACE }
  | "}"      { RBRACE }
  | "["      { LBRACK }
  | "]"      { RBRACK }
  | ","      { COMMA }
  | "="      { EQUALS }
  | ">"      { GT }
  | ">="     { GE }
  | "=="     { EQ }
  | "!="     { NE }
  | "<"      { LT }
  | "<="     { LE }
  | "&&"     { AND }
  | "&"      { AMP }
  | "^"      { CARET }
  | "||"     { OR }
  | ";"      { SEMICOLON }
  | ":"      { COLON }
  | "->"     { ARROW }
  | "?"      { QUESTION }
  | "'"      { read_char lexbuf }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | eof      { EOF }
  | _ { raise (Syntax_error ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and in_comment =
  parse
  | newline { new_line lexbuf; in_comment lexbuf }
  | "[*"    { incr nested_comment_count; in_comment lexbuf }
  | "*]"    { 
      decr nested_comment_count; 
      if !nested_comment_count > 0 then in_comment lexbuf
      else read lexbuf 
    }
  | _       { in_comment lexbuf }
  | eof     { raise (Syntax_error "Unterminated comment") }

and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  (* NOTE: because we print this stuff to a C file, we don't need to do this *)
  | '\\' '/'  (* { Buffer.add_char buf '/'; read_string buf lexbuf } *)
  | '\\' '\\' (* { Buffer.add_char buf '\\'; read_string buf lexbuf } *)
  | '\\' '"' (* { Buffer.add_char buf '"'; read_string buf lexbuf } *)
  | '\\' 'b'  (* { Buffer.add_char buf '\b'; read_string buf lexbuf } *)
  | '\\' 'f'  (* { Buffer.add_char buf '\012'; read_string buf lexbuf } *)
  | '\\' 'n'  (* { Buffer.add_char buf '\n'; read_string buf lexbuf } *)
  | '\\' 'r'  (* { Buffer.add_char buf '\r'; read_string buf lexbuf } *)
  | '\\' 't'  (* { Buffer.add_char buf '\t'; read_string buf lexbuf } *)
  | '\\' '0'  (* { Buffer.add_char buf '\0'; read_string buf lexbuf } *)
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Syntax_error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Syntax_error ("String is not terminated")) }

and read_char =
  parse
  (* NOTE: because we print this stuff to a C file, we don't need to do this *)
  | '\\' '/' '\''  (* { CHAR "/"  }*) 
  | '\\' '\\' '\'' (* { CHAR "\\" }*)
  | '\\' 'b' '\''  (* { CHAR "\b" }*)
  | '\\' 'n' '\''  (* { CHAR "\n" }*)
  | '\\' 'r' '\''  (* { CHAR "\r" }*)
  | '\\' 't' '\''  (* { CHAR "\t" }*)
  | '\\' ''' '\''  (* { CHAR "\'" }*)
  | '\\' '0' '\''  (* { CHAR '\0' }*)
  | [^ '\'' '\\'] '\''  { CHAR (Lexing.lexeme lexbuf) }
  | _ { raise (Syntax_error ("Illegal char character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Syntax_error ("Char is not terminated")) }