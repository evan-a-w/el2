open! Core

module Make () = struct
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

  module Set = struct
    include Set.Make (T)

    let hash_fold_t (hash_state : Ppx_hash_lib.Std.Hash.state) t :
        Ppx_hash_lib.Std.Hash.state =
      Set.fold ~init:hash_state
        ~f:(fun hash_state key -> [%hash_fold: string] hash_state key)
        t
  end

  include T
  include Hashable.Make (T)
end
