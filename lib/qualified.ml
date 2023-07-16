open! Core

type 'a t = Qualified of Uppercase.t * 'a t | Unqualified of 'a
[@@deriving sexp, compare, equal, hash]

type qualifications = Uppercase.t Sequence.t [@@deriving compare, equal]

let sexp_of_qualifications qualifications =
  [%sexp_of: Uppercase.t list] (Sequence.to_list qualifications)

module Make (Arg : sig
  type arg [@@deriving sexp, compare, equal, hash]
end) =
struct
  module T = struct
    type t = Qualified of Uppercase.t * t | Unqualified of Arg.arg
    [@@deriving sexp, compare, equal, hash]
  end

  module Map = struct
    include Map.Make (T)

    let hash_fold_t (type a) hash_fold_a
        (hash_state : Ppx_hash_lib.Std.Hash.state) t :
        Ppx_hash_lib.Std.Hash.state =
      Map.fold ~init:hash_state
        ~f:(fun ~key ~data hash_state ->
          [%hash_fold: T.t * a] hash_state (key, data))
        t
  end

  include T
end

let prepend t ~qualifications =
  List.fold qualifications ~init:t ~f:(fun t qualification ->
      Qualified (qualification, t))

let qualifications_of_t t : qualifications =
  Sequence.unfold ~init:t ~f:(function
    | Qualified (qualification, t) -> Some (qualification, t)
    | Unqualified _ -> None)
