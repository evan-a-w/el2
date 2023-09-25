open! Core
open! Shared
open! Frontend
open Ty

exception Field_left_only of string
exception Field_right_only of string

let occurs_check a mono =
  let free_vars = free_ty_vars mono in
  match Set.mem free_vars a with
  | true -> Type_error.fail (Type_error.Occurs_check (a, mono))
  | false -> ()
;;

let rec unify_mem_rep mono_a mono_b a b =
  let a = condense_mem_rep a in
  let b = condense_mem_rep b in
  let fail () =
    Type_error.fail (Type_error.Unification_error (mono_a, mono_b))
  in
  match a, b with
  | (#base_mem_rep as a'), (#base_mem_rep as b') when equal_base_mem_rep a' b'
    -> ()
  | #base_mem_rep, #base_mem_rep -> fail ()
  | `Product a, `Product b | `Sum a, `Sum b ->
    (match List.zip a b with
     | Base.List.Or_unequal_lengths.Unequal_lengths -> fail ()
     | Ok l -> List.iter l ~f:(fun (a, b) -> unify_mem_rep mono_a mono_b a b))
  | `Var a, `Var b when phys_equal a b -> ()
  | `Var r, _ -> r := b
  | _, `Var r -> r := a
  | _ -> fail ()
;;

let rec unify_var mono1 ty_var mono2 =
  occurs_check ty_var.Ty.ty_var_name mono2;
  let mem_rep = Ty.condense_mem_rep ty_var.equiv_mem_rep in
  let mem_rep' = Ty.mem_rep_of_mono mono2 in
  unify_mem_rep mono1 mono2 mem_rep mem_rep';
  ty_var.equiv_mono := mono2

and unify mono1 mono2 =
  let mono1 = condense mono1 in
  let mono2 = condense mono2 in
  let unification_error () =
    Type_error.fail (Type_error.Unification_error (mono1, mono2))
  in
  match mono1, mono2 with
  | Named p1, Named p2 -> unify_type_proof p1 p2
  | Ty_var x, Ty_var y when phys_equal x y -> ()
  | Ty_var x, _ -> unify_var mono1 x mono2
  | _, Ty_var x -> unify_var mono2 x mono1
  | Weak x, Weak y when phys_equal x y -> ()
  | Weak x, _ -> unify_var mono1 x mono2
  | _, Weak x -> unify_var mono2 x mono1
  | Reference x, Reference y -> unify x y
  | Closure (x1, x2, c1), Closure (y1, y2, c2) ->
    unify_mem_rep
      mono1
      mono2
      (mem_rep_of_closure_info c1)
      (mem_rep_of_closure_info c2);
    unify x1 y1;
    unify x2 y2
  | Tuple l1, Tuple l2 -> unify_lists ~unification_error l1 l2
  | _ -> unification_error ()

and unify_type_proof a b =
  let unification_error () =
    Type_error.fail (Type_error.Unification_error (Named a, Named b))
  in
  let a = condense_type_proof a in
  let b = condense_type_proof b in
  let monos1 = Map.data a.tyvar_map |> List.map ~f:condense in
  let monos2 = Map.data b.tyvar_map |> List.map ~f:condense in
  match same_type_proof a b with
  | true -> unify_lists ~unification_error monos1 monos2
  | false -> unification_error ()

and unify_lists ~unification_error l1 l2 =
  let zipped =
    match List.zip l1 l2 with
    | Unequal_lengths -> unification_error ()
    | Ok zipped -> zipped
  in
  let f (mono1, mono2) = unify mono1 mono2 in
  List.iter zipped ~f
;;
