open! Core

module Type_expr = struct
  type t = Single of string | Multi of t list * t [@@deriving sexp, variants]
end
