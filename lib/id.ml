open! Core

(* this is so ugly holy*)

module Make () = struct
  module T = struct
    type t = int [@@deriving sexp, compare, equal, hash]
  end

  module Map = struct
    include Map.Make (T)

    let hash_fold_t
      (type a)
      hash_fold_a
      (hash_state : Ppx_hash_lib.Std.Hash.state)
      t
      : Ppx_hash_lib.Std.Hash.state
      =
      Map.fold
        ~init:hash_state
        ~f:(fun ~key ~data hash_state ->
          [%hash_fold: int * a] hash_state (key, data))
        t
    ;;
  end

  module Set = struct
    module T = struct
      include Set.Make (T)

      let hash_fold_t (hash_state : Ppx_hash_lib.Std.Hash.state) t
        : Ppx_hash_lib.Std.Hash.state
        =
        Set.fold
          ~init:hash_state
          ~f:(fun hash_state key -> [%hash_fold: int] hash_state key)
          t
      ;;

      let hash = Hashtbl.hash
    end

    module Map = struct
      module Map = Core.Map.Make (T)

      let hash_fold_t
        (type a)
        hash_fold_a
        (hash_state : Ppx_hash_lib.Std.Hash.state)
        t
        : Ppx_hash_lib.Std.Hash.state
        =
        Map.fold
          ~init:hash_state
          ~f:(fun ~key ~data hash_state ->
            [%hash_fold: T.t * a] hash_state (key, data))
          t
      ;;

      include Map
    end

    include T
    include Hashable.Make (T)
  end

  include T
  include Hashable.Make (T)
end
