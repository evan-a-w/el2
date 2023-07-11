open! Core

module Mode = struct
  type t = Allocation of [ `Local | `Global ]
  [@@deriving sexp, compare, equal, hash, variants]
end

module Tag = struct
  type t = {
    type_expr : Types.Type_expr.t option; [@sexp.option]
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
  | Var of binding
  | Unit
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Wrapped of t
[@@deriving sexp]

and binding = (string * Tag.t option[@sexp.option]) [@@deriving sexp]
and t = { tag : Tag.t option; [@sexp.option] node : node } [@@deriving sexp]

let untagged node = { tag = None; node }
let node_of_t (t : t) = match t.tag with Some _ -> Wrapped t | None -> t.node
