open! Core
open! Shared
open! Frontend

exception Field_left_only of string
exception Field_right_only of string

let occurs_check a mono =
  let free_vars = Ty.free_ty_vars mono in
  match Set.mem free_vars a with
  | true -> Type_error.fail (Type_error.Occurs_check (a, mono))
  | false -> ()
;;

let unify_mem_rep mono_a mono_b a b =
  if Mem_rep.equal_base a b then () else Type_error.fail (Type_error.Unification_error (mono_a, mono_b))
;;
