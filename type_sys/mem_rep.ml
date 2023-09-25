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
    | `Var of string * t ref
    ]
  [@@deriving sexp, equal, compare]
end

module Set = Set.Make (T)
module Map = Map.Make (T)
include T

let rec condense t =
  match t with
  | `Var (_, r) ->
    if phys_equal t !r
    then t
    else (
      let t' = condense !r in
      r := t';
      t')
  | _ -> t
;;
