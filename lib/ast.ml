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

module Qualified = struct
  type 'a t = Qualified of Uppercase.t * 'a t | Unqualified of 'a
  [@@deriving sexp, compare, equal, hash]
end

module Tuple = struct
  type 'a t = 'a list [@@deriving sexp, compare, equal, hash]
end

module Type_expr = struct
  type t =
    | Single of Lowercase.t Qualified.t
    | Tuple of t Tuple.t Qualified.t
    | Multi of t * t
  [@@deriving sexp, variants, compare, hash, equal]
end

module Type_def_lit = struct
  type t =
    | Record of Type_expr.t Lowercase.Map.t
    | Enum of Type_expr.t Uppercase.Map.t
    | Type_expr of Type_expr.t
  [@@deriving sexp, variants, equal, hash, compare]
end

module Mode = struct
  type t = Allocation of [ `Local | `Global ]
  [@@deriving sexp, compare, equal, hash, variants]
end

module Tag = struct
  type t = {
    type_expr : Type_expr.t option; [@sexp.option]
    mode : Mode.t option; [@sexp.option]
    others : (string * Token.t list) list; [@sexp.list]
  }
  [@@deriving sexp, compare, equal, hash, fields]

  let empty = { type_expr = None; mode = None; others = [] }
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
  type t =
    | Name of Lowercase.t
    | Constructor of Uppercase.t Qualified.t * t option
    | Literal of Literal.t
    | Record of t Lowercase.Map.t Qualified.t
    | Tuple of t Tuple.t Qualified.t
    | Typed of t * Tag.t
  [@@deriving sexp, equal, hash, compare, variants]
end

type node =
  | Lambda of Binding.t * t
  | App of node * node
  | Let of Binding.t * t * t
  | If of t * t * t
  | Var of Binding.t Qualified.t
  | Literal of Literal.t
  | Tuple of node Tuple.t Qualified.t
  | Wrapped of t Qualified.t
[@@deriving sexp, equal, hash, compare]

and t = { tag : Tag.t option; [@sexp.option] node : node } [@@deriving sexp]

module Toplevel = struct
  type nonrec t =
    | Type_def of { name : Lowercase.t; expr : Type_def_lit.t }
    | Let of { binding : Binding.t; expr : t }
  [@@deriving sexp, equal, hash, compare]
end

let untagged node = { tag = None; node }

let node_of_t (t : t) =
  match t.tag with
  | Some _ -> Wrapped (Qualified.Unqualified t)
  | None -> t.node
