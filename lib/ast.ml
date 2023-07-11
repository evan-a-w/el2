open! Core

type lowercase = string [@@deriving sexp, compare, equal, hash]
type uppercase = string [@@deriving sexp, compare, equal, hash]

module Qualified = struct
  type 'a t = Qualified of uppercase * 'a t | Unqualified of 'a
  [@@deriving sexp, compare, equal, hash]
end

module Type_expr = struct
  type t = Single of lowercase Qualified.t | Multi of t list * t
  [@@deriving sexp, variants, compare, hash, equal]
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

type node =
  | Lambda of binding * t
  | App of node * node
  | Let of binding * t * t
  | If of t * t * t
  | Var of binding Qualified.t
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Wrapped of t Qualified.t
[@@deriving sexp]

and binding = (lowercase * Tag.t option[@sexp.option]) [@@deriving sexp]
and t = { tag : Tag.t option; [@sexp.option] node : node } [@@deriving sexp]

let untagged node = { tag = None; node }

let node_of_t (t : t) =
  match t.tag with
  | Some _ -> Wrapped (Qualified.Unqualified t)
  | None -> t.node
