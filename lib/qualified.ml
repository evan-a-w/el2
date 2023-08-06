open! Core

type 'a t = Qualified of Uppercase.t * 'a t | Unqualified of 'a
[@@deriving sexp, compare, equal, hash]

type qualifications = Uppercase.t List.t [@@deriving compare, equal, hash, sexp]

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

let rec split t =
  match t with
  | Qualified (qualification, t) ->
      let qualifications, a = split t in
      (qualification :: qualifications, a)
  | Unqualified a -> ([], a)

let qualifications_of_t t : qualifications = split t |> fst

let show show_a t =
  let rec loop t =
    match t with
    | Qualified (qualification, t) -> qualification ^ "." ^ loop t
    | Unqualified a -> show_a a
  in
  loop t

let append t uppercase =
  let rec loop t =
    match t with
    | Qualified (qualification, t) -> Qualified (qualification, loop t)
    | Unqualified _ -> Qualified (uppercase, t)
  in
  loop t

let pop t =
  let rec loop t =
    match t with
    | Qualified (q, (Unqualified _ as x)) -> (Some q, x)
    | Qualified (qualification, t) ->
        let q, r = loop t in
        (q, Qualified (qualification, r))
    | Unqualified _ -> (None, t)
  in
  loop t

let full_qualifications (t : Uppercase.t t) =
  let rec loop t =
    match t with
    | Qualified (q, t) -> q :: loop t
    | Unqualified name -> [ name ]
  in
  loop t
