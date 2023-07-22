open! Core

type t = Contravariant | Covariant | Invariant
[@@deriving sexp, variants, compare, hash, equal, show]

let merge t1 t2 = if equal t1 t2 then t1 else Invariant
