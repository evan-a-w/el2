open! Core

module Make (Arg : sig
  type t [@@deriving sexp, equal, compare]
end) =
struct
  module Map = Map.Make (Arg)

  type t = (Arg.t * int) Map.t [@@deriving sexp, equal, compare]

  let empty = Map.empty

  let add t mono =
    match Map.add t ~key:mono ~data:(mono, 1) with
    | `Duplicate -> t
    | `Ok t -> t

  let rec find_with_size t mono : (Arg.t * int) * t =
    match Map.find t mono with
    | Some (mono', sz) when [%equal: Arg.t] mono mono' -> ((mono, sz), t)
    | Some (mono', _) ->
        let data, t' = find_with_size t mono' in
        let t' = Map.set t' ~key:mono' ~data in
        (data, t')
    | None ->
        let t = add t mono in
        ((mono, 1), t)

  let find t mono =
    let (res, _), t = find_with_size t mono in
    (res, t)

  let union t mono1 mono2 : t =
    let res1, t = find_with_size t mono1 in
    let res2, t = find_with_size t mono2 in
    match (res1, res2) with
    | (mono1, _), (mono2, _) when [%equal: Arg.t] mono1 mono2 -> t
    | (mono1, sz1), (mono2, sz2) ->
        let (a, sza), (b, szb) =
          if sz1 >= sz2 then ((mono1, sz1), (mono2, sz2))
          else ((mono2, sz2), (mono1, sz1))
        in
        let t = Map.set t ~key:b ~data:(a, sza + szb) in
        let t = Map.set t ~key:a ~data:(a, sza + szb) in
        t
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
            let res, _ = String_ufds.find_with_size t x in
            res)
      in
      print_s [%sexp (results : (string * int) list)];
      [%expect {| ((a 5) (a 5) (a 5) (a 5) (a 5) (z 1) (x 2) (x 2)) |}]
  end)
