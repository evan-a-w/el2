open! Core
open! Shared
open! Frontend

type 'a single =
  [ `Bits0
  | `Bits8
  | `Bits16
  | `Bits32
  | `Bits64
  | (* For now these are 64 bits *)
    `Reg
  | `Pointer of 'a
  ]
[@@deriving sexp, equal, hash, compare]

module rec T : sig
  type mem_rep =
    [ abstract single
    | `Union of Abstract.t list
    | `Native_struct of (Lowercase.t * abstract) list
    | `C_struct of (Lowercase.t * abstract) list
    ]
  [@@deriving sexp, equal, hash, compare]

  and abstract =
    | Closed of mem_rep
    | Any of Lowercase.t (* refers to same tyvar as mono *)
  [@@deriving sexp, equal, hash, compare]
end = struct
  type mem_rep =
    [ abstract single
    | `Union of Abstract.t list
    | `Native_struct of (Lowercase.t * abstract) list
    | `C_struct of (Lowercase.t * abstract) list
    ]
  [@@deriving sexp, equal, hash, compare]

  and abstract =
    | Closed of mem_rep
    | Any of Lowercase.t (* refers to same tyvar as mono *)
  [@@deriving sexp, equal, hash, compare]
end

and Abstract : sig
  type t = T.abstract [@@deriving sexp, equal, hash, compare]

  module Set : Hash_fold_set.S with type arg := t
end = struct
  module T = struct
    type t = T.abstract [@@deriving sexp, equal, hash, compare]
  end

  module Set = Hash_fold_set.Make (T)
  include T
end

include T

type single_mem_rep = abstract single [@@deriving sexp, equal, hash, compare]

(* I don't think i need this at this point!!!! *)
module Size_class = struct
  module rec T : sig
    type t =
      | Size of int
      | Var of Lowercase.t
      | Max of Size_class_set.t
      | Struct of t Lowercase.Map.t
    [@@deriving sexp, equal, compare]
  end = struct
    type t =
      | Size of int
      | Var of Lowercase.t
      | Max of Size_class_set.t
      | Struct of t Lowercase.Map.t
    [@@deriving sexp, equal, compare]
  end

  and Size_class_set : (Set_intf.S with type Elt.t = T.t) = Set.Make (T)

  module Map = struct
    include Map.Make (T)

    let add_int t ~key ~data = Map.add t ~key:(T.Size key) ~data
  end

  include T

  let max t1 t2 =
    match t1, t2 with
    | Max l1, Max l2 -> Max (Set.union l1 l2)
    | Size a, Size b -> Size (max a b)
    | Var a, Var b when Lowercase.equal a b -> Var a
    | Max l, x | x, Max l -> Max (Set.add l x)
    | _ -> Max (Size_class_set.of_list [ t1; t2 ])
  ;;
end

let class_single ~equivalences mem_rep =
  match mem_rep with
  | `Bits0 -> Size_class.Map.add_int equivalences ~key:0 ~data:mem_rep
  | `Bits8 -> Size_class.Map.add_int equivalences ~key:1 ~data:mem_rep
  | `Bits16 -> Size_class.Map.add_int equivalences ~key:2 ~data:mem_rep
  | `Bits32 -> Size_class.Map.add_int equivalences ~key:4 ~data:mem_rep
  | `Bits64 | `Reg | `Pointer _ ->
    Size_class.Map.add_int equivalences ~key:8 ~data:mem_rep
;;

(* | `Union x -> *)
(*   let max = Uppercase.Map.fold x ~init:None ~f:(fun ~key:_ ~data acc -> *)
(*       match acc with *)
(*       | None -> Some data *)
(*       | Some other -> Size_class.max data other *)
(*              ) in *)

module Abstract_ufds = Ufds.Make (Abstract)

let find x =
  let open State.Result.Let_syntax in
  let%bind ufds = State.Result.get in
  let x, ufds = Abstract_ufds.find ufds x in
  let%map () = State.Result.put ufds in
  x
;;

let union x y =
  let open State.Result.Let_syntax in
  let%bind ufds = State.Result.get in
  let ufds = Abstract_ufds.union ufds x y in
  let%map () = State.Result.put ufds in
  ()
;;

let rec unify x y =
  let open State.Result.Let_syntax in
  let%bind x = find x in
  let%bind y = find y in
  if phys_equal x y
  then return ()
  else (
    match x, y with
    | Closed x, Closed y -> unify_mem_rep x y
    | (Any _ as v), o | o, (Any _ as v) -> union v o)

and unify_mem_rep (x : mem_rep) (y : mem_rep) =
  let unification_error () =
    State.Result.error
      [%message "Unification error" (x : mem_rep) (y : mem_rep)]
  in
  let open State.Result.Let_syntax in
  match x, y with
  | `Bits0, `Bits0 -> return ()
  | `Bits8, `Bits8 -> return ()
  | `Bits16, `Bits16 -> return ()
  | `Bits32, `Bits32 -> return ()
  | (`Bits64 | `Reg | `Pointer (_ : Abstract.t)), (`Bits64 | `Reg | `Pointer _)
    -> return ()
  | `Union x, `Union y ->
    let%bind x = State.Result.all @@ List.map ~f:find x in
    let%bind y = State.Result.all @@ List.map ~f:find y in
    (match List.zip x y with
     | Ok l -> State.Result.all_unit @@ List.map l ~f:(fun (x, y) -> unify x y)
     | Unequal_lengths -> unification_error ())
  | `Native_struct x, `Native_struct y ->
    let%bind x = State.Result.all @@ List.map ~f:(fun (_, x) -> find x) x in
    let%bind y = State.Result.all @@ List.map ~f:(fun (_, x) -> find x) y in
    let%bind y = State.Result.all @@ List.map ~f:find y in
    (match List.zip x y with
     | Ok l -> State.Result.all_unit @@ List.map l ~f:(fun (x, y) -> unify x y)
     | Unequal_lengths -> unification_error ())
  | `C_struct x, `C_struct y ->
    let%bind x = State.Result.all @@ List.map ~f:(fun (_, x) -> find x) x in
    let%bind y = State.Result.all @@ List.map ~f:(fun (_, x) -> find x) y in
    let%bind y = State.Result.all @@ List.map ~f:find y in
    (match List.zip x y with
     | Ok l -> State.Result.all_unit @@ List.map l ~f:(fun (x, y) -> unify x y)
     | Unequal_lengths -> unification_error ())
  | _ -> unification_error ()
;;
