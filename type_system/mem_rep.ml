open! Core
open! Shared
open! Frontend

type mem_rep =
  | Bits0
  | Bits8
  | Bits16
  | Bits32
  | Bits64
  | Reg
  | Union of abstract Uppercase.Map.t
  | Native_struct of abstract Lowercase.Map.t
  | C_struct of (Lowercase.t * abstract) list
[@@deriving sexp, equal, hash, compare]

and abstract =
  | Closed of mem_rep
  | Any of Lowercase.t (* refers to same tyvar as mono *)
[@@deriving sexp, equal, hash, compare]

module Size_class = struct
  module rec T : sig
    type t =
      | Size of int
      | Var of Lowercase.t
      | Max of Size_class_set.t
    [@@deriving sexp, equal, compare]
  end = struct
    type t =
      | Size of int
      | Var of Lowercase.t
      | Max of Size_class_set.t
    [@@deriving sexp, equal, compare]
  end

  and Size_class_set : (Set_intf.S with type Elt.t = T.t) = Set.Make (T)

  module Map = struct
    include Map.Make (T)

    let add_int t ~key ~data = add t ~key:(T.Size key) ~data
    let add_var t ~key ~data = add t ~key:(T.Var key) ~data
    let add_max t ~key ~data = add t ~key:(T.Max key) ~data
  end

  include T

  let max t1 t2 =
    match t1, t2 with
    | Max l1, Max l2 -> Max (Size_class_set.union l1 l2)
    | Size a, Size b -> Size (max a b)
    | Var a, Var b when Lowercase.equal a b -> Var a
    | Max l, x | x, Max l -> Max (Size_class_set.add l x)
    | _ -> Max (Size_class_set.of_list [ t1; t2 ])
  ;;
end

let rec class_mem_reps ~equivalences mem_rep =
  match mem_rep with
  | Bits0 -> Size_class.Map.add_int equivalences ~key:0 ~data:mem_rep
  | Bits8 -> Size_class.Map.add_int equivalences ~key:1 ~data:mem_rep
  | Bits16 -> Size_class.Map.add_int equivalences ~key:2 ~data:mem_rep
  | Bits32 -> Size_class.Map.add_int equivalences ~key:4 ~data:mem_rep
  | Bits64 -> Size_class.Map.add_int equivalences ~key:8 ~data:mem_rep
  | Reg ->
    Size_class.Map.add_int
      equivalences
      ~key:8
      ~data:mem_rep (* very portable :)))))) *)
  | Union x ->
    Map.fold x ~init:equivalences ~f:(fun ~key:_ ~data acc ->
      class_mem_reps ~equivalences:acc data)
;;

(* TODO: make not terbl *)
let c_struct_of_native native =
  native |> Map.to_alist |> List.map ~f:(fun (k, v) -> k, v)
;;

let rec equal_mem_rep x y =
  match x, y with
  | Bits0, Bits0 -> true
  | Bits8, Bits8 -> true
  | Bits16, Bits16 -> true
  | Bits32, Bits32 -> true
  | Bits64, Bits64 -> true
  | Reg, Reg -> true
  | Union x, Union y -> Map.equal equal_abstract x y
  | Native_struct x, Native_struct y -> Map.equal equal_abstract x y
  | C_struct x, C_struct y ->
    List.equal (Tuple2.equal ~eq1:Lowercase.equal ~eq2:equal_abstract) x y
  | (C_struct _ as c_struct), Native_struct n
  | Native_struct n, (C_struct _ as c_struct) ->
    equal_mem_rep c_struct (C_struct (c_struct_of_native n))
  | _ -> false

and equal_abstract x y =
  match x, y with
  | Closed x, Closed y -> equal_mem_rep x y
  | Any x, Any y -> Lowercase.equal x y
  | _ -> false
;;

let unify x y =
  if phys_equal x y
  then Ok x
  else (
    match x, y with
    | Closed x, Closed y when equal_mem_rep x y -> Ok (Closed x)
    | Closed x, Closed y ->
      Error
        [%message
          "Memory representations don't match" (x : mem_rep) (y : mem_rep)]
    | Any _, o | o, Any _ -> Ok o)
;;
