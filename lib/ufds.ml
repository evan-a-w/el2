open! Core

module Make (Arg : sig
    type t [@@deriving sexp, equal, compare]
  end) =
struct
  module Map = Map.Make (Arg)

  type t = Arg.t Map.t [@@deriving sexp, equal, compare]

  let empty = Map.empty

  let add t mono =
    match Core.Map.add t ~key:mono ~data:mono with
    | `Duplicate -> t
    | `Ok t -> t
  ;;

  let rec find t mono : Arg.t * t =
    match Core.Map.find t mono with
    | Some mono' when [%equal: Arg.t] mono mono' -> mono, t
    | Some mono' ->
      let data, t' = find t mono' in
      let t' = Core.Map.set t' ~key:mono' ~data in
      data, t'
    | None ->
      let t = add t mono in
      mono, t
  ;;

  let union t mono1 mono2 : t =
    let mono1, t = find t mono1 in
    let mono2, t = find t mono2 in
    match [%equal: Arg.t] mono1 mono2 with
    | true -> t
    | false ->
      let t = Core.Map.set t ~key:mono2 ~data:mono1 in
      t
  ;;
end

let%test_module _ =
  (module struct
    module String_ufds = Make (String)

    let%expect_test _ =
      let t = String_ufds.empty in
      let t = String_ufds.union t "a" "b" in
      let t = String_ufds.union t "b" "c" in
      let t = String_ufds.union t "d" "e" in
      let t = String_ufds.union t "a" "d" in
      let t = String_ufds.add t "z" in
      let t = String_ufds.union t "x" "y" in
      let results =
        List.map [ "a"; "b"; "c"; "d"; "e"; "z"; "x"; "y" ] ~f:(fun x ->
          let res, _ = String_ufds.find t x in
          res)
      in
      print_s [%sexp (results : string list)];
      [%expect {| (a a a a a z x x) |}]
    ;;
  end)
;;
