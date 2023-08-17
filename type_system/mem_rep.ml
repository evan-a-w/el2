open! Core
open! Shared
open! Frontend

type concrete =
  | Bits8
  | Bits16
  | Bits32
  | Bits64
  | Reg
  | Union of concrete Uppercase.Map.t
  | Native_struct of concrete Lowercase.Map.t
  | C_struct of (Lowercase.t * concrete) list
[@@deriving sexp, equal, hash, compare]

let c_struct_of_native native =
  native |> Map.to_alist |> List.map ~f:(fun (k, v) -> k, v)
;;

let equal_concrete x y =
  match x, y with
  | Bits8, Bits8 -> true
  | Bits16, Bits16 -> true
  | Bits32, Bits32 -> true
  | Bits64, Bits64 -> true
  | Reg, Reg -> true
  | Union x, Union y -> Map.equal equal_concrete x y
  | Native_struct x, Native_struct y -> Map.equal equal_concrete x y
  | C_struct x, C_struct y ->
    List.equal (Tuple2.equal ~eq1:Lowercase.equal ~eq2:equal_concrete) x y
  | (C_struct _ as c_struct), Native_struct n
  | Native_struct n, (C_struct _ as c_struct) ->
    equal_concrete c_struct (C_struct (c_struct_of_native n))
  | _ -> false
;;

type abstract =
  | Concrete of concrete
  | Var of abstract ref

let rec reach_end x =
  match x with
  | Concrete _ -> x
  | Var x' when phys_equal !x' x -> x
  | Var x -> reach_end !x
;;

let unify x y =
  let x = reach_end x in
  let y = reach_end y in
  if phys_equal x y
  then Ok ()
  else (
    match x, y with
    | Concrete x, Concrete y when equal_concrete x y -> Ok ()
    | Concrete x, Concrete y ->
      Error
        [%message
          "Memory representations don't match" (x : concrete) (y : concrete)]
    | Var x, _ | _, Var x ->
      x := y;
      Ok ())
;;
