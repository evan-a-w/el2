open! Core
open Types
open PPrint

let mynest i x = ifflat x (break 0 ^^ blank i ^^ align x)

module M = Set.Make (struct
    type t = mono list * string [@@deriving sexp, compare]
  end)

let rec mono ?(map = ref M.empty) (t : mono) : PPrint.document =
  let mono = mono ~map in
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
    | `User inst -> inst_user_type ~map inst
  in
  group res

and user_type_p ?(map = ref M.empty) user_type =
  let mono = mono ~map in
  let inner user_type =
    match !(user_type.info) with
    | Some (`Alias m) -> string "alias" ^^ space ^^ mono m
    | Some (`Enum l) ->
      string "enum"
      ^^ space
      ^^ lbracket
      ^^ space
      ^^ mynest
           4
           (List.map l ~f:(fun (s, m) ->
              match m with
              | None -> string s
              | Some m -> string s ^^ space ^^ string "=" ^^ space ^^ mono m)
            |> separate (semi ^^ space))
      ^^ space
      ^^ rbracket
    | Some (`Struct l) ->
      string "struct"
      ^^ space
      ^^ lbracket
      ^^ space
      ^^ mynest
           4
           (List.map l ~f:(fun (s, m) ->
              string s ^^ space ^^ string ":" ^^ space ^^ mono m)
            |> separate (semi ^^ space))
      ^^ space
      ^^ rbracket
    | None -> string "unknown"
  in
  string user_type.repr_name
  ^^ (match user_type.ty_vars with
      | [] -> empty
      | l ->
        lparen
        ^^ mynest 4 (List.map l ~f:string |> separate (comma ^^ space))
        ^^ rparen)
  ^^ space
  ^^ equals
  ^^ space
  ^^ inner user_type

and inst_user_type ?(map = ref M.empty) inst =
  let mono = mono ~map in
  match Set.mem !map (inst.monos, inst.orig_user_type.repr_name) with
  | false -> short_inst_user_type inst
  | _ ->
    let orig_user_type = user_type_p ~map inst.orig_user_type in
    map := Set.add !map (inst.monos, inst.orig_user_type.repr_name);
    let user_type = get_insted_user_type inst |> Option.value_exn in
    let monos = mono (`Tuple inst.monos) in
    let user_type = user_type_p ~map user_type in
    lbrace
    ^^ space
    ^^ string "orig_user_type"
    ^^ space
    ^^ equals
    ^^ space
    ^^ orig_user_type
    ^^ semi
    ^^ space
    ^^ string "insted_user_type"
    ^^ space
    ^^ equals
    ^^ space
    ^^ user_type
    ^^ semi
    ^^ space
    ^^ string "monos"
    ^^ space
    ^^ equals
    ^^ space
    ^^ lbracket
    ^^ monos
    ^^ rbracket
    ^^ space
    ^^ rbrace

and short_inst_user_type inst =
  let monos =
    match inst.monos with
    | [] -> empty
    | monos ->
      lparen ^^ (List.map monos ~f:mono |> separate (comma ^^ space)) ^^ rparen
  in
  string inst.orig_user_type.repr_name ^^ monos
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

let top_var (var : _ Typed_ast.top_var) : PPrint.document =
  match var with
  | Typed_ast.El { name; _ }
  | Typed_ast.Extern (name, _, _)
  | Typed_ast.Implicit_extern (name, _, _) -> string name
  | Typed_ast.From_functor (name, _) -> string name
;;

let rec typed_ast (t : _ Typed_ast.expr) =
  let expr_inner =
    match fst t with
    | `Unit -> string "()"
    | `Null -> string "null"
    | `Int i -> Int.to_string i |> string
    | `Float f -> Float.to_string f |> string
    | `String s -> "\"" ^ s ^ "\"" |> string
    | `Bool b -> Bool.to_string b |> string
    | `Char c -> "'" ^ Char.to_string c ^ "'" |> string
    | `Glob_var (var, _) -> top_var var
    | `Local_var s -> string s
    | `Break a -> string "break" ^^ space ^^ typed_ast a
    | `Loop a -> string "loop" ^^ space ^^ typed_ast a
    | `Array_lit l ->
      let inner = List.map l ~f:typed_ast |> separate (semi ^^ space) in
      lbrace ^^ char '|' ^^ mynest 4 inner ^^ char '|' ^^ rbrace
    | `Tuple l ->
      let inner = List.map l ~f:typed_ast |> separate (comma ^^ space) in
      mynest 4 inner |> wrap
    | `Enum (s, e) ->
      (match e with
       | None -> string s
       | Some e -> string s ^^ wrap (typed_ast e))
    | `Struct l ->
      let inner =
        List.map l ~f:(fun (s, e) ->
          string s ^^ space ^^ string "=" ^^ space ^^ typed_ast e)
        |> separate (semi ^^ space)
      in
      lbrace ^^ space ^^ mynest 4 inner ^^ space ^^ rbrace
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
      lbrace ^^ break 1 ^^ mynest 4 (typed_ast l) ^^ break 1 ^^ rbrace
    | `Access_enum_field (s, e) ->
      typed_ast e ^^ space ^^ string "@" ^^ space ^^ string s
    | `Check_variant (s, e) ->
      typed_ast e ^^ space ^^ string "is" ^^ space ^^ string s
    | `Assert e -> string "assert" ^^ space ^^ typed_ast e
    | `Unsafe_cast e -> string "unsafe_cast" ^^ lparen ^^ typed_ast e ^^ rparen
    | `Size_of m -> string "sizeof" ^^ lbracket ^^ mono m ^^ rbracket
    | `Return e -> string "return" ^^ lparen ^^ typed_ast e ^^ rparen
  in
  let mono = snd t |> mono in
  expr_inner ^^ space ^^ colon ^^ space ^^ mono
;;

type t = PPrint.document

let to_string x =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. 80 buf x;
  Buffer.contents buf
;;

let output_endline ?prefix x =
  let prefix =
    Option.map prefix ~f:(fun x -> string x) |> Option.value ~default:empty
  in
  PPrint.ToChannel.pretty 1. 80 stdout (prefix ^^ x ^^ hardline)
;;

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
