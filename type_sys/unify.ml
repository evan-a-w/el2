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
  let a = Mem_rep.condense a in
  let b = Mem_rep.condense b in
  let fail () =
    Type_error.fail (Type_error.Unification_error (mono_a, mono_b))
  in
  match a, b with
  | (#Mem_rep.base as a'), (#Mem_rep.base as b') when Mem_rep.equal a' b' -> ()
  | #Mem_rep.base, #Mem_rep.base -> fail ()
  | `Var (a, _), `Var (b, _) when Lowercase.equal a b -> ()
  | `Var (_, r), _ -> r := b
  | _, `Var (_, r) -> r := a
;;

let rec unify_var make mono1 x mono2 =
  occurs_check x mono2;
  let m, _ = Mem_rep.Abstract_ufds.find state.mem_rep_ufds (Mem_rep.Any x) in
  let mem_rep = mem_rep_of_mono mono2 in
  let%bind () = unify_mem_rep m mem_rep in
  let new_tyvar = make x in
  let%bind () = State.map (union new_tyvar mono1) ~f:Result.return in
  State.map (union mono2 new_tyvar) ~f:Result.return

and unify mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind mono1 = reach_end mono1 in
  let%bind mono2 = reach_end mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match mono1, mono2 with
  | Named p1, Named p2 -> unify_type_proof p1 p2
  | TyVar x, TyVar y when String.equal x y -> State.Result.return ()
  | TyVar x, _ -> unify_var (fun x -> TyVar x) mono1 x mono2
  | _, TyVar x -> unify_var (fun x -> TyVar x) mono2 x mono1
  | Weak x, Weak y when String.equal x y -> State.Result.return ()
  | Weak x, _ -> unify_var (fun x -> Weak x) mono1 x mono2
  | _, Weak x -> unify_var (fun x -> Weak x) mono2 x mono1
  | Reference x, Reference y -> unify x y
  | Function (x1, x2), Function (y1, y2) ->
    let%bind () = unify x1 y1 in
    unify x2 y2
  | Function (x1, x2), Closure (y1, y2, { closure_mem_rep; _ })
  | Closure (x1, x2, { closure_mem_rep; _ }), Function (y1, y2) ->
    let%bind () = unify_mem_rep closure_mem_rep (Mem_rep.Closed `Bits0) in
    let%bind () = unify x1 y1 in
    unify x2 y2
  | ( Closure (x1, x2, { closure_mem_rep = m1; _ })
    , Closure (y1, y2, { closure_mem_rep = m2; _ }) ) ->
    let%bind () = unify x1 y1 in
    let%bind () = unify x2 y2 in
    unify_mem_rep m1 m2
  | Tuple l1, Tuple l2 -> unify_lists ~unification_error l1 l2
  | _ -> unification_error ()

and unify_type_proof a b =
  let open State.Result.Let_syntax in
  let unification_error () = unification_error (Named a) (Named b) in
  let%bind ({ type_id = id1; tyvar_map = rep1; _ } as a) =
    reach_end_type_proof a
  in
  let%bind ({ type_id = id2; tyvar_map = rep2; _ } as b) =
    reach_end_type_proof b
  in
  let monos1 = Map.data rep1 in
  let%bind monos1 = State.Result.all (List.map ~f:reach_end monos1) in
  let monos2 = Map.data rep2 in
  let%bind monos2 = State.Result.all (List.map ~f:reach_end monos2) in
  match phys_equal id1 id2 with
  | true -> unify_lists ~unification_error monos1 monos2
  | false ->
    let%bind.State.Result a = show_type_proof a in
    let%bind.State.Result b = show_type_proof b in
    State.Result.error
      [%message "types failed to unify" ~_:(a : string) ~_:(b : string)]

and unify_lists ~unification_error l1 l2 =
  let open State.Result.Let_syntax in
  let%bind zipped =
    match List.zip l1 l2 with
    | Unequal_lengths -> unification_error ()
    | Ok zipped -> return zipped
  in
  let f (mono1, mono2) = unify mono1 mono2 in
  State.Result.all_unit (List.map zipped ~f)
;;
