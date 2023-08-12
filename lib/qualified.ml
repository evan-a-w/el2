open! Core

type 'a t =
  | Qualified of Uppercase.t * 'a t
  | Unqualified of 'a
[@@deriving sexp, compare, equal, hash]

type qualifications = Uppercase.t List.t [@@deriving compare, equal, hash, sexp]

module Make (Arg : sig
  type t [@@deriving sexp, compare, equal, hash]
end) =
struct
  module T = struct
    type nonrec t = Arg.t t [@@deriving sexp, compare, equal, hash]
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
          [%hash_fold: T.t * a] hash_state (key, data))
        t
    ;;
  end

  include T
end

let prepend t ~qualifications =
  List.fold qualifications ~init:t ~f:(fun t qualification ->
    Qualified (qualification, t))
;;

let rec split t =
  match t with
  | Qualified (qualification, t) ->
    let qualifications, a = split t in
    qualification :: qualifications, a
  | Unqualified a -> [], a
;;

let qualifications_of_t t : qualifications = split t |> fst

let show show_a t =
  let rec loop t =
    match t with
    | Unqualified a -> show_a a
    | Qualified (qualification, t) ->
      (match qualification with
       | "" -> loop t
       | _ -> qualification ^ "." ^ loop t)
  in
  loop t
;;

let append t uppercase =
  let rec loop t =
    match t with
    | Qualified (qualification, t) -> Qualified (qualification, loop t)
    | Unqualified _ -> Qualified (uppercase, t)
  in
  loop t
;;

let pop t =
  let rec loop t =
    match t with
    | Qualified (q, (Unqualified _ as x)) -> Some q, x
    | Qualified (qualification, t) ->
      let q, r = loop t in
      q, Qualified (qualification, r)
    | Unqualified _ -> None, t
  in
  loop t
;;

let full_qualifications (t : Uppercase.t t) =
  let rec loop t =
    match t with
    | Qualified (q, t) -> q :: loop t
    | Unqualified name -> [ name ]
  in
  loop t
;;

let map t ~f =
  let rec loop t =
    match t with
    | Qualified (q, t) -> Qualified (q, loop t)
    | Unqualified a -> Unqualified (f a)
  in
  loop t
;;

let map_m t ~f =
  let open State.Result.Let_syntax in
  let rec loop t =
    match t with
    | Qualified (q, t) ->
      let%map res = loop t in
      Qualified (q, res)
    | Unqualified a ->
      let%map a = f a in
      Unqualified a
  in
  loop t
;;

let pprint_t pp_a =
  let rec loop t =
    match t with
    | Qualified (q, t) -> PPrint.(string q ^^ dot ^^ loop t)
    | Unqualified a -> pp_a a
  in
  loop
;;

let%expect_test "pretty print" =
  let a = Qualified ("A", Qualified ("B", Unqualified "C")) in
  let pp_a = PPrint.string in
  PPrint.ToChannel.pretty 1. 80 Out_channel.stdout (pprint_t pp_a a);
  [%expect {|
    A.B.C |}]
;;
