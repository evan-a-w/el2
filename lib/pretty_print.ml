open! Core
open Types
open PPrint

let mynest i x = ifflat x (hardline ^^ blank i ^^ align x)

module M = Set.Make (struct
    type t = mono list * user_type [@@deriving sexp, compare]
  end)

let rec mono (t : mono) : PPrint.document =
  let res =
    match inner_mono t with
    | `Unit -> string "unit"
    | `Bool -> string "bool"
    | `I64 -> string "i64"
    | `F64 -> string "f64"
    | `Char -> string "char"
    | `C_int -> string "c_int"
    | `Pointer t -> string "&" ^^ mono t
    | `Tuple l ->
      let inner =
        List.map l ~f:(fun x -> mono x) |> separate (string "," ^^ space)
      in
      lparen ^^ mynest 4 inner ^^ rparen
    | `Var (s, _) -> string s
    | `Indir (i, _) -> string [%string "weak_%{i#Int}"]
    | `Function (a, b) ->
      mono a ^^ space ^^ string "->" ^^ mynest 4 (space ^^ mono b)
    | `Opaque t' -> string "opaque" ^^ lbracket ^^ mono t' ^^ rbracket
    | `User inst -> inst_user_type inst
  in
  group res

and inst_user_type inst =
  let monos =
    match inst.monos with
    | [] -> empty
    | monos ->
      lparen
      ^^ mynest 4 (List.map monos ~f:mono |> separate (comma ^^ space))
      ^^ rparen
  in
  string (user_type inst).repr_name ^^ monos
;;

let inf_op (op : Ast.inf_op) : PPrint.document =
  match op with
  | `Ge -> string ">="
  | `Rem -> string "%"
  | `Div -> string "/"
  | `Add -> string "+"
  | `Lt -> string "<"
  | `And -> string "&&"
  | `Sub -> string "-"
  | `Eq -> string "=="
  | `Le -> string "<="
  | `Or -> string "||"
  | `Gt -> string ">"
  | `Mul -> string "*"
  | `Ne -> string "!="
;;

let pref_op (op : Ast.pref_op) : PPrint.document =
  match op with
  | `Minus -> string "-"
;;

let wrap x = lparen ^^ x ^^ rparen

let rec typed_ast (t : Typed_ast.expr) =
  let expr_inner =
    match fst t with
    | `Unit -> string "()"
    | `Null -> string "null"
    | `Int i -> Int.to_string i |> string
    | `Float f -> Float.to_string f |> string
    | `String s -> "\"" ^ s ^ "\"" |> string
    | `Bool b -> Bool.to_string b |> string
    | `Char c -> "'" ^ Char.to_string c ^ "'" |> string
    | `Glob_var (s, _) -> string s
    | `Local_var s -> string s
    | `Tuple l ->
      let inner = List.map l ~f:typed_ast |> separate (comma ^^ space) in
      mynest 4 inner |> wrap
    | `Enum (s, e) ->
      (match e with
       | None -> string s
       | Some e -> string s ^^ wrap (typed_ast e))
    | `Struct (n, l) ->
      let inner =
        List.map l ~f:(fun (s, e) ->
          string s ^^ space ^^ string "=" ^^ space ^^ typed_ast e)
        |> separate (semi ^^ space)
      in
      char '#'
      ^^ string n
      ^^ space
      ^^ lbrace
      ^^ space
      ^^ mynest 4 inner
      ^^ space
      ^^ rbrace
    | `Apply (a, b) ->
      wrap (typed_ast a)
      ^^ wrap (break 0 ^^ (mynest 4 @@ typed_ast b) ^^ break 0)
    | `Inf_op (op, a, b) ->
      wrap (typed_ast a ^^ space ^^ inf_op op ^^ space ^^ typed_ast b)
    | `Pref_op (op, a) -> pref_op op ^^ typed_ast a
    | `Deref e -> char '*' ^^ typed_ast e
    | `Ref e -> char '&' ^^ typed_ast e
    | `Tuple_access (e, i) ->
      wrap (typed_ast e) ^^ char '.' ^^ string (Int.to_string i)
    | `Field_access (e, s) -> wrap (typed_ast e) ^^ dot ^^ string s
    | `Index (a, b) -> wrap (typed_ast a) ^^ lbracket ^^ typed_ast b ^^ rbracket
    | `If (a, b, c) ->
      string "if"
      ^^ break 1
      ^^ mynest 4 (typed_ast a)
      ^^ break 1
      ^^ string "then"
      ^^ break 1
      ^^ mynest 4 (typed_ast b)
      ^^ break 1
      ^^ string "else"
      ^^ break 1
      ^^ mynest 4 (typed_ast c)
    | `Let (s, a, b) ->
      group
        (string "let"
         ^^ space
         ^^ string s
         ^^ space
         ^^ string "="
         ^^ space
         ^^ typed_ast a
         ^^ space
         ^^ string "in")
      ^^ break 1
      ^^ typed_ast b
    | `Assign (a, b) ->
      typed_ast a ^^ space ^^ string "=" ^^ space ^^ typed_ast b
    | `Compound l ->
      lbrace
      ^^ break 1
      ^^ mynest 4 (separate (semi ^^ break 1) (List.map l ~f:typed_ast))
      ^^ break 1
      ^^ rbrace
    | `Access_enum_field (s, e) ->
      typed_ast e ^^ space ^^ string "@" ^^ space ^^ string s
    | `Check_variant (s, e) ->
      typed_ast e ^^ space ^^ string "is" ^^ space ^^ string s
    | `Assert e -> string "assert" ^^ space ^^ typed_ast e
  in
  let mono = snd t |> mono in
  expr_inner ^^ space ^^ colon ^^ space ^^ mono
;;

let output_endline x = PPrint.ToChannel.pretty 1. 80 stdout (x ^^ hardline)

let print ~name ~poly ~typed_ast:t =
  let doc =
    string name
    ^^ space
    ^^ mynest
         4
         (colon
          ^^ space
          ^^ string (Types.show_poly poly)
          ^^ space
          ^^ char '='
          ^^ space
          ^^ typed_ast t)
    ^^ hardline
  in
  output_endline doc
;;
