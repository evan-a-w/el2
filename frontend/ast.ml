open! Core
open! Shared
module Tag = String_replacement.Make ()

module Tuple = struct
  type 'a t = 'a list [@@deriving sexp, compare, equal, hash]

  let pprint_t pprint_a l =
    let open PPrint in
    let rec loop = function
      | [] -> string ""
      | [ x ] -> pprint_a x
      | x :: xs -> pprint_a x ^^ string ", " ^^ loop xs
    in
    string "(" ^^ loop l ^^ string ")"
  ;;
end

module Type_expr = struct
  type t =
    | Pointer of t
    | Single of Lowercase.t Qualified.t
    | Arrow of t * t
    | Tuple of t Tuple.t
    | Multi of t * Lowercase.t Qualified.t
  [@@deriving sexp, variants, compare, hash, equal]

  let rec pprint_t =
    let open PPrint in
    function
    | Pointer t -> char '@' ^^ pprint_t t
    | Single x -> Qualified.pprint_t string x
    | Arrow (x, y) -> pprint_t x ^^ string " -> " ^^ pprint_t y
    | Tuple l -> Tuple.pprint_t pprint_t l
    | Multi (x, y) -> pprint_t x ^^ char ' ' ^^ Qualified.pprint_t string y
  ;;
end

module Type_binding = struct
  type arg =
    | Single of (Variance.t * Lowercase.t)
    | Tuple of (Variance.t * Lowercase.t) list
  [@@deriving sexp, variants, equal, hash, compare]

  (* need to enforce that every arg appears in the definition *)
  type t =
    | Mono of Lowercase.t
    | Poly of (arg * Lowercase.t)
  [@@deriving sexp, variants, equal, hash, compare]
end

module Type_def_lit = struct
  type t =
    | Record of (Lowercase.t * (Type_expr.t * [ `Mutable | `Immutable ])) List.t
    | Enum of (Uppercase.t * Type_expr.t option) List.t
    | Type_expr of Type_expr.t
  [@@deriving sexp, variants, equal, hash, compare]
end

module Mode = struct
  type t = Allocation of [ `Local | `Global ]
  [@@deriving sexp, compare, equal, hash, variants]

  let to_string = function
    | Allocation `Local -> "local"
    | Allocation `Global -> "global"
  ;;
end

module Ast_tags = struct
  type t = Token.t list Tag.Map.t [@@deriving sexp, compare, equal, hash]

  let empty = Tag.Map.empty
end

module Value_tag = struct
  type t =
    { type_expr : Type_expr.t option [@sexp.option]
    ; mode : Mode.t option [@sexp.option]
    ; ast_tags : Ast_tags.t
    }
  [@@deriving sexp, compare, equal, hash, fields]

  let empty = { type_expr = None; mode = None; ast_tags = Ast_tags.empty }

  let pprint_t t =
    let open PPrint in
    let type_expr =
      match type_expr t with
      | None -> empty
      | Some t -> string " : " ^^ Type_expr.pprint_t t
    in
    let tag_list = ast_tags t |> Tag.Map.to_alist in
    let tag_list =
      match mode t with
      | None -> tag_list
      | Some m -> ("mode", [ Token.Symbol (Mode.to_string m) ]) :: tag_list
    in
    let each_tag tag tokens =
      string tag ^^ string ": " ^^ separate_map (break 1) Token.pprint_t tokens
    in
    let tags =
      match tag_list with
      | [] -> empty
      | _ ->
        let inner =
          separate_map
            (string ", " ^^ break 1)
            (fun (tag, tokens) -> each_tag tag tokens)
            tag_list
        in
        break 1 ^^ string "#[" ^^ inner ^^ string "]"
    in
    type_expr ^^ tags
  ;;
end

module Literal = struct
  type t =
    | Unit
    | Int of int
    | Bool of bool
    | Float of float
    | String of string
    | Char of char
  [@@deriving sexp, equal, hash, compare]

  let pretty_print_t = function
    | Unit -> PPrint.string "()"
    | Int i -> Int.to_string i |> PPrint.string
    | Bool b -> Bool.to_string b |> PPrint.string
    | Float f -> Float.to_string f |> PPrint.string
    | String s -> PPrint.dquotes (PPrint.string s)
    | Char c -> PPrint.squotes (PPrint.char c)
  ;;
end

let pprint_record pprint_a map =
  let open PPrint in
  let lhs =
    if Lowercase.Map.is_empty map
    then string "{}"
    else
      Lowercase.Map.fold map ~init:empty ~f:(fun ~key ~data acc ->
        let curr =
          string key ^^ string " : " ^^ pprint_a data ^^ char ';' ^^ break 1
        in
        acc ^^ curr)
  in
  group (char '{' ^^ nest 2 lhs ^^ char '}')
;;

module Binding = struct
  module T = struct
    type t =
      | Name of Lowercase.t
      | Constructor of Uppercase.t Qualified.t * t option
      | Literal of Literal.t
      | Record of t Lowercase.Map.t Qualified.t
      | Tuple of t Tuple.t Qualified.t
      | Typed of t * Value_tag.t
      | Renamed of t * Lowercase.t
      | Pointer of t
    [@@deriving sexp, equal, hash, compare, variants]
  end

  module Table = Map.Make (T)
  include T

  let rec iter_names (t : t) ~f =
    match t with
    | Name s -> f s
    | Constructor (_, None) | Literal _ -> ()
    | Constructor (_, Some t) -> iter_names t ~f
    | Record r -> Qualified.iter ~f:(Lowercase.Map.iter ~f:(iter_names ~f)) r
    | Tuple l -> Qualified.iter ~f:(List.iter ~f:(iter_names ~f)) l
    | Typed (t, _) -> iter_names t ~f
    | Renamed (t, s) ->
      iter_names t ~f;
      f s
    | Pointer t -> iter_names t ~f
  ;;

  let rec pprint_t =
    let open PPrint in
    function
    | Name x -> string x
    | Constructor (x, None) -> Qualified.pprint_t string x
    | Constructor (x, Some y) ->
      Qualified.pprint_t string x ^^ nest 2 (break 1 ^^ pprint_t y)
    | Literal l -> Literal.pretty_print_t l
    | Record r ->
      Qualified.map ~f:(pprint_record pprint_t) r |> Qualified.pprint_t Fn.id
    | Tuple t ->
      Qualified.map ~f:(Tuple.pprint_t pprint_t) t |> Qualified.pprint_t Fn.id
    | Typed (t, value_tag) ->
      char '('
      ^^ pprint_t t
      ^^ break 1
      ^^ Value_tag.pprint_t value_tag
      ^^ char ')'
    | Renamed (t, x) -> pprint_t t ^^ string " as " ^^ string x
    | Pointer t -> char '@' ^^ pprint_t t
  ;;
end

type 'type_def type_description =
  { type_name : Type_binding.t
  ; type_def : 'type_def
  ; ast_tags : Ast_tags.t
  }
[@@deriving sexp, equal, hash, compare]

type toplevel_type =
  | Sig_binding of Binding.t * Value_tag.t
  | Sig_module of module_sig module_description
  | Sig_type_def of Type_def_lit.t option type_description
[@@deriving sexp, equal, hash, compare]

and module_sig = toplevel_type list [@@deriving sexp, equal, hash, compare]

and 'module_sig module_description =
  { module_name : Uppercase.t
  ; functor_args : (Uppercase.t * module_sig) list
  ; module_sig : 'module_sig
  }
[@@deriving sexp, equal, hash, compare]

type rec_flag = bool [@@deriving sexp, equal, hash, compare]

(* node has no spaces, t does *)
type node =
  | Var of Lowercase.t Qualified.t
  | Literal of Literal.t
  | Tuple of expr Tuple.t Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and let_each = Binding.t * expr [@@deriving sexp, equal, hash, compare]

and let_def =
  | Rec of let_each list
  | Nonrec of let_each
[@@deriving sexp, equal, hash, compare]

and module_def =
  | Struct of toplevel list
  | Named of Uppercase.t Qualified.t
  | Functor_app of Uppercase.t Qualified.t * module_def list
  | Module_typed of module_def * module_sig
[@@deriving sexp, equal, hash, compare]

and expr =
  | Node of node
  | If of expr * expr * expr
  | Lambda of Binding.t * expr
  | App of
      expr
      * expr (* these should just be node | App but that makes it more clunky *)
  | Let_in of let_def * expr
  | Ref of expr
  | Deref of expr
  | Field_access of expr * Lowercase.t Qualified.t
  | Field_set of (expr * Lowercase.t Qualified.t * expr)
  | Match of expr * (Binding.t * expr) list
  | Typed of expr * Value_tag.t
[@@deriving sexp, equal, hash, compare]

and toplevel =
  | Type_def of Type_def_lit.t type_description
  | Let of let_def
  (* TODO: | Module_type of Uppercase.t * module_sig *)
  | Module_def of
      { module_description : module_sig option module_description
      ; module_def : module_def
      }
[@@deriving sexp, equal, hash, compare]

and t = toplevel list [@@deriving sexp, equal, hash, compare]

let rec pprint_node node =
  match node with
  | Literal l -> Literal.pretty_print_t l
  | Var s -> Qualified.pprint_t PPrint.string s
  | Tuple l ->
    Qualified.map ~f:(Tuple.pprint_t pprint_expr) l |> Qualified.pprint_t Fn.id
  | Constructor s -> Qualified.pprint_t PPrint.string s
  | Record r ->
    Qualified.map ~f:(pprint_record pprint_expr) r |> Qualified.pprint_t Fn.id
  | Wrapped e ->
    Qualified.map ~f:(fun e -> PPrint.(char '(' ^^ pprint_expr e ^^ char ')')) e
    |> Qualified.pprint_t Fn.id

and pprint_expr_no_spaces =
  let open PPrint in
  function
  | Node node -> pprint_node node
  | expr -> char '(' ^^ pprint_expr expr ^^ char ')'

and pprint_expr =
  let open PPrint in
  function
  | Node node -> pprint_node node
  | If (pred, then_, else_) ->
    group
      (string "if"
       ^^ nest 2 (break 1 ^^ pprint_expr pred)
       ^^ break 1
       ^^ string "then"
       ^^ nest 2 (break 1 ^^ pprint_expr then_)
       ^^ break 1
       ^^ string "else"
       ^^ nest 2 (break 1 ^^ pprint_expr else_))
  | Lambda (binding, expr) ->
    group
      (group
         (string "fun"
          ^^ break 1
          ^^ Binding.pprint_t binding
          ^^ break 1
          ^^ string "->")
       ^^ nest 2 (break 1 ^^ pprint_expr expr))
  | App (a, b) ->
    group (pprint_expr a ^^ nest 2 (break 1 ^^ pprint_expr_no_spaces b))
  | Let_in (Nonrec let_each, expr2) ->
    pprint_x_in (pprint_let_each "let" let_each) expr2
  | Let_in (Rec let_each_list, expr2) ->
    let hd, let_each_list =
      match let_each_list with
      | [] -> failwith "empty let rec"
      | hd :: tl -> hd, tl
    in
    let init = pprint_let_each "let rec" hd in
    let lhs =
      List.fold let_each_list ~init ~f:(fun acc let_each ->
        acc ^^ break 1 ^^ pprint_let_each "and" let_each)
    in
    pprint_x_in lhs expr2
  | Ref expr -> group (char '@' ^^ pprint_expr expr)
  | Deref expr -> group (char '!' ^^ pprint_expr expr)
  | Field_access (lhs, field) ->
    group
      (pprint_expr lhs
       ^^ char '.'
       ^^ nest 2 (break 0 ^^ Qualified.pprint_t PPrint.string field))
  | Field_set (lhs, field, rhs) ->
    group
      (pprint_expr lhs
       ^^ char '.'
       ^^ nest 2 (break 0 ^^ Qualified.pprint_t PPrint.string field)
       ^^ break 1
       ^^ string "<-"
       ^^ nest 2 (break 1 ^^ pprint_expr rhs))
  | Match (expr, cases) ->
    group
      (string "match"
       ^^ nest 2 (break 1 ^^ pprint_expr expr)
       ^^ break 1
       ^^ string "with"
       ^^ break 1
       ^^ string "| "
       ^^ separate_map
            (break 1 ^^ string "| ")
            (fun (binding, expr) ->
              group
                (Binding.pprint_t binding
                 ^^ nest
                      2
                      (break 1
                       ^^ string "->"
                       ^^ nest 2 (break 1 ^^ pprint_expr expr))))
            cases)
  | Typed (expr, value_tag) ->
    group (pprint_expr expr ^^ nest 2 (Value_tag.pprint_t value_tag))

and pprint_let_each s (binding, expr) =
  let open PPrint in
  group
    (string s ^^ break 1 ^^ Binding.pprint_t binding ^^ break 1 ^^ string "=")
  ^^ break 1
  ^^ nest 2 (pprint_expr expr)

and pprint_x_in x expr =
  let open PPrint in
  group (x ^^ break 1 ^^ string "in" ^^ break 1 ^^ pprint_expr expr)
;;
