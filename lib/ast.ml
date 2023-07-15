open! Core

module String_replacement () = struct
  module T = struct
    type t = string [@@deriving sexp, compare, equal, hash]
  end

  module Map = struct
    include Map.Make (T)

    let hash_fold_t (type a) hash_fold_a
        (hash_state : Ppx_hash_lib.Std.Hash.state) t :
        Ppx_hash_lib.Std.Hash.state =
      Map.fold ~init:hash_state
        ~f:(fun ~key ~data hash_state ->
          [%hash_fold: string * a] hash_state (key, data))
        t
  end

  include T
  include Hashable.Make (T)
end

module Lowercase = String_replacement ()
module Uppercase = String_replacement ()
module Tag = String_replacement ()

module Qualified = struct
  type 'a t = Qualified of Uppercase.t * 'a t | Unqualified of 'a
  [@@deriving sexp, compare, equal, hash]
end

module Tuple = struct
  type 'a t = 'a list [@@deriving sexp, compare, equal, hash]
end

module Type_expr = struct
  type t =
    | Pointer of t
    | Single of Lowercase.t Qualified.t
    | Tuple of t Tuple.t Qualified.t
    | Multi of t * t
  [@@deriving sexp, variants, compare, hash, equal]
end

module Type_def_lit = struct
  type t =
    | Record of Type_expr.t Lowercase.Map.t
    | Enum of Type_expr.t option Uppercase.Map.t
    | Type_expr of Type_expr.t
  [@@deriving sexp, variants, equal, hash, compare]
end

module Mode = struct
  type t = Allocation of [ `Local | `Global ]
  [@@deriving sexp, compare, equal, hash, variants]
end

module Ast_tags = struct
  type t = Token.t list Tag.Map.t [@@deriving sexp, compare, equal, hash]

  let empty = Tag.Map.empty
end

module Value_tag = struct
  type t = {
    type_expr : Type_expr.t option; [@sexp.option]
    mode : Mode.t option; [@sexp.option]
    ast_tags : Ast_tags.t;
  }
  [@@deriving sexp, compare, equal, hash, fields]

  let empty = { type_expr = None; mode = None; ast_tags = Ast_tags.empty }
end

module Literal = struct
  type t =
    | Unit
    | Int of int
    | Bool of bool
    | Float of float
    | String of string
  [@@deriving sexp, equal, hash, compare]
end

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
    [@@deriving sexp, equal, hash, compare, variants]
  end

  module Table = Map.Make (T)
  include T
end

type 'type_def type_description = {
  type_name : Type_expr.t;
  type_def : 'type_def;
  ast_tags : Ast_tags.t;
}
[@@deriving sexp, equal, hash, compare]

type toplevel_type =
  | Sig_binding of Binding.t * Value_tag.t
  | Sig_module of module_sig module_description
  | Sig_type_def of Type_def_lit.t option type_description
[@@deriving sexp, equal, hash, compare]

and module_sig = toplevel_type list [@@deriving sexp, equal, hash, compare]

and 'module_sig module_description = {
  module_name : Uppercase.t;
  functor_args : (Uppercase.t * module_sig) list;
  module_sig : 'module_sig;
}
[@@deriving sexp, equal, hash, compare]

(* node has no spaces, t does *)
type node =
  | Var of Lowercase.t Qualified.t
  | Literal of Literal.t
  | Tuple of expr Tuple.t Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and let_def = { binding : Binding.t; expr : expr }
[@@deriving sexp, equal, hash, compare]

and module_def =
  | Struct of toplevel list
  | Named of Uppercase.t Qualified.t
  | Functor_app of module_def * module_def list
  | Module_typed of module_def * module_sig
[@@deriving sexp, equal, hash, compare]

and expr =
  | Node of node
  | If of expr * expr * expr
  | Lambda of Binding.t * expr
  | App of
      expr
      * expr (* these should just be node | App but that makes it more clunky *)
  | Let_in of Binding.t * expr * expr
  | Match of expr * (Binding.t * expr) list
  | Typed of expr * Value_tag.t
  | Module of module_def
[@@deriving sexp, equal, hash, compare]

and toplevel =
  | Type_def of Type_def_lit.t type_description
  | Let of let_def
  (* TODO: | Module_type of Uppercase.t * module_sig *)
  | Module_def of {
      module_description : module_sig option module_description;
      module_def : module_def;
    }
[@@deriving sexp, equal, hash, compare]

and t = toplevel list [@@deriving sexp, equal, hash, compare]
