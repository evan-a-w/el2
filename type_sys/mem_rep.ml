open! Core
open! Shared
open! Frontend

type base =
  [ `Bits0
  | `Bits8
  | `Bits16
  | `Bits32
  | `Bits64
  ]
[@@deriving sexp, equal, hash, compare]

module T = struct
  type t =
    [ base
    | `Union of t list
    | `Struct of t list
    ]
  [@@deriving sexp, equal, hash, compare]
end

module Set = Set.Make (T)
module Map = Map.Make (T)

include T
