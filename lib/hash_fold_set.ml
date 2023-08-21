open! Core

module type S = sig
  type arg

  include Set_intf.S with type Elt.t = arg

  val hash_fold_t
    :  Ppx_hash_lib.Std.Hash.state
    -> t
    -> Ppx_hash_lib.Std.Hash.state

  val hash : t -> int
end

module Make (Arg : sig
  type t [@@deriving sexp, compare, equal, hash]
end) : S with type arg := Arg.t = struct
  module T = struct
    module Arg = Arg
    include Set.Make (Arg)

    let hash_fold_t (hash_state : Ppx_hash_lib.Std.Hash.state) t
      : Ppx_hash_lib.Std.Hash.state
      =
      Set.fold
        ~init:hash_state
        ~f:(fun hash_state key -> [%hash_fold: Arg.t] hash_state key)
        t
    ;;

    let hash = Hashtbl.hash
  end

  module type S = module type of T

  include T
end
