open! Core
open! Shared
open! Frontend
open! Ty
open! Inference_state
open! Type_defs
open! Monos

exception Field_left_only of string
exception Field_right_only of string

let unification_error mono1 mono2 =
  let%bind.State.Result a = show_mono mono1 in
  let%bind.State.Result b = show_mono mono2 in
  State.Result.error
    [%message "failed to unify types" ~_:(a : string) ~_:(b : string)]
;;

let occurs_check a mono =
  let open State.Result.Let_syntax in
  let free_vars = free_ty_vars mono in
  match Set.mem free_vars a with
  | true ->
    State.Result.error
      [%message "occurs check failed" (a : Lowercase.t) (mono : mono)]
  | false -> return ()
;;

let rec reach_end_mono_type_proof type_proof : mono state_result_m =
  match%bind.State lookup_type_map type_proof.type_id with
  | Ok (_, _, { type_name; type_id; _ })
    when not @@ phys_equal type_id type_proof.type_id ->
    reach_end_mono_type_proof { type_proof with type_name; type_id }
  | _ -> State.Result.return @@ Named type_proof
;;

let rec reach_end_type_proof type_proof : type_proof state_result_m =
  match%bind.State lookup_type_map type_proof.type_id with
  | Ok (_, _, { type_name; type_id; _ })
    when not @@ phys_equal type_id type_proof.type_id ->
    reach_end_type_proof { type_proof with type_name; type_id }
  | _ -> State.Result.return type_proof
;;

let reach_end (mono : mono) =
  let%bind.State mono = find mono in
  match mono with
  | Named type_proof ->
    let%map.State.Result x = reach_end_type_proof type_proof in
    Named x
  | _ -> State.Result.return mono
;;

let reach_end_mono (mono : mono) =
  let%bind.State mono = find mono in
  match mono with
  | Named type_proof -> reach_end_mono_type_proof type_proof
  | mono -> State.Result.return mono
;;

let unify_mem_rep' f m1 m2 =
  let open State.Result.Let_syntax in
  let%bind m1 = on_mem_rep_ufds ~f:(Mem_rep.find m1) in
  let%bind m2 = on_mem_rep_ufds ~f:(Mem_rep.find m2) in
  on_mem_rep_ufds ~f:(f m1 m2)
;;

let unify_mem_rep = unify_mem_rep' Mem_rep.unify
let unify_mem_rep_less_general = unify_mem_rep' Mem_rep.unify_less_general

let lookup_and_inst_binding_poly binding_id =
  let open State.Result.Let_syntax in
  let%bind { poly; _ } = lookup_binding_id binding_id in
  inst_result poly
;;

let rec unify_var cons mono1 x m mono2 =
  let open State.Result.Let_syntax in
  let%bind () = occurs_check x mono2 in
  let mem_rep = mem_rep_of_mono mono2 in
  let%bind () = unify_mem_rep m mem_rep in
  let%bind state = State.Result.get in
  let m, _ = Mem_rep.Abstract_ufds.find state.mem_rep_ufds m in
  let new_tyvar = cons x m in
  let%bind () = State.map (union new_tyvar mono1) ~f:Result.return in
  State.map (union mono2 new_tyvar) ~f:Result.return

and unify mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind mono1 = reach_end mono1 in
  let%bind mono2 = reach_end mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match mono1, mono2 with
  | Named p1, Named p2 -> unify_type_proof p1 p2
  | TyVar (x, _), TyVar (y, _) when String.equal x y -> State.Result.return ()
  | TyVar (x, m), _ -> unify_var (fun x y -> TyVar (x, y)) mono1 x m mono2
  | _, TyVar (x, m) -> unify_var (fun x y -> TyVar (x, y)) mono2 x m mono1
  | Weak (x, _), Weak (y, _) when String.equal x y -> State.Result.return ()
  | Weak (x, m), _ -> unify_var (fun x y -> Weak (x, y)) mono1 x m mono2
  | _, Weak (x, m) -> unify_var (fun x y -> Weak (x, y)) mono2 x m mono1
  | Reference x, Reference y -> unify x y
  | Function (x1, x2), Function (y1, y2) ->
    let%bind () = unify x1 y1 in
    unify x2 y2
  | ( Function (x1, x2)
    , Closure (y1, y2, { closure_mem_rep = Mem_rep.Closed `Bits0; _ }) )
  | ( Closure (x1, x2, { closure_mem_rep = Mem_rep.Closed `Bits0; _ })
    , Function (y1, y2) ) ->
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

let rec unify_less_general mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind mono1 = reach_end mono1 in
  let%bind mono2 = reach_end mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match mono1, mono2 with
  | Named p1, Named p2 -> unify_less_general_type_proof ~unification_error p1 p2
  | TyVar (x, _), TyVar (y, _) when String.equal x y -> State.Result.return ()
  | TyVar _, _ -> unification_error ()
  | _, TyVar (x, _) ->
    let%bind () = occurs_check x mono1 in
    State.map (union mono1 mono2) ~f:Result.return
  | Weak (x, _), Weak (y, _) when String.equal x y -> State.Result.return ()
  | Weak _, _ -> unification_error ()
  | _, Weak (x, _) ->
    let%bind () = occurs_check x mono1 in
    State.map (union mono1 mono2) ~f:Result.return
  | Reference x, Reference y -> unify_less_general x y
  | Function (x1, x2), Function (y1, y2) ->
    let%bind () = unify_less_general x1 y1 in
    unify_less_general x2 y2
  | ( Function (x1, x2)
    , Closure (y1, y2, { closure_mem_rep = Mem_rep.Closed `Bits0; _ }) )
  | ( Closure (x1, x2, { closure_mem_rep = Mem_rep.Closed `Bits0; _ })
    , Function (y1, y2) ) ->
    let%bind () = unify_less_general x1 y1 in
    unify_less_general x2 y2
  | ( Closure (x1, x2, { closure_mem_rep = m1; _ })
    , Closure (y1, y2, { closure_mem_rep = m2; _ }) ) ->
    let%bind () = unify_less_general x1 y1 in
    let%bind () = unify_less_general x2 y2 in
    unify_mem_rep_less_general m1 m2
  | Tuple l1, Tuple l2 -> unify_less_general_lists ~unification_error l1 l2
  | _ -> unification_error ()

and unify_less_general_type_proof ~unification_error a b =
  let open State.Result.Let_syntax in
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
  | true -> unify_less_general_lists ~unification_error monos1 monos2
  | false ->
    let%bind.State.Result a = show_type_proof a in
    let%bind.State.Result b = show_type_proof b in
    State.Result.error
      [%message
        "types failed to unify_less_general" ~_:(a : string) ~_:(b : string)]

and unify_less_general_lists ~unification_error l1 l2 =
  let open State.Result.Let_syntax in
  let%bind zipped =
    match List.zip l1 l2 with
    | Unequal_lengths -> unification_error ()
    | Ok zipped -> return zipped
  in
  let f (mono1, mono2) = unify_less_general mono1 mono2 in
  State.Result.all_unit (List.map zipped ~f)
;;

let rec unify_module_bindings
  ~(signature : Typed_ast.module_)
  ~(definition : Typed_ast.module_)
  =
  let open State.Result.Let_syntax in
  let%bind joined_vars =
    try
      return
      @@ Map.merge
           signature.toplevel_vars
           definition.toplevel_vars
           ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with
    | Field_left_only key ->
      State.Result.error
        [%message "Value in signature not in definition" (key : Lowercase.t)]
  in
  let%bind () =
    Map.fold
      joined_vars
      ~init:(return ())
      ~f:(fun ~key:_ ~data:(left, right) acc ->
        let%bind () = acc in
        let _, sig_val = List.hd_exn left |> fst |> split_poly in
        let _, def_val = List.hd_exn right |> fst |> split_poly in
        unify_less_general sig_val def_val)
  in
  let%bind joined_type_constructors =
    try
      return
      @@ Map.merge
           signature.toplevel_type_constructors
           definition.toplevel_type_constructors
           ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with
    | Field_left_only key ->
      State.Result.error
        [%message
          "Type constructor in signature not in definition" (key : Lowercase.t)]
  in
  let%bind type_constructors =
    Map.fold
      joined_type_constructors
      ~init:(return Lowercase.Map.empty)
      ~f:(fun ~key ~data:(left, right) acc ->
        let%bind acc = acc in
        let%bind arg1, u1, p1 = lookup_type_map left in
        let%bind ((arg2, u2, p2) as r) = lookup_type_map right in
        let%bind () =
          match equal_type_proof { p1 with type_id = p2.type_id } p2 with
          | true -> return ()
          | false ->
            State.Result.error
              [%message
                "Type constructor proofs do not match"
                  (p1 : type_proof)
                  (p2 : type_proof)]
        in
        let%bind () =
          match Option.equal equal_type_constructor_arg arg1 arg2 with
          | true -> return ()
          | false ->
            State.Result.error
              [%message
                "Type constructor arguments do not match"
                  (arg1 : type_constructor_arg option)
                  (arg2 : type_constructor_arg option)]
        in
        let%bind () =
          match equal_user_type u1 u2 with
          | true -> return ()
          | false ->
            State.Result.error
              [%message "Types not equal" (u1 : user_type) (u2 : user_type)]
        in
        let%map () = set_type_map ~type_id:p1.type_id r in
        Map.add_exn ~key ~data:right acc)
  in
  let%bind joined_modules =
    try
      return
      @@ Map.merge
           signature.toplevel_modules
           definition.toplevel_modules
           ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with
    | Field_left_only key ->
      State.Result.error
        [%message "Module in signature not in definition" (key : Uppercase.t)]
  in
  let%bind () =
    Map.fold
      joined_modules
      ~init:(return ())
      ~f:(fun ~key:_ ~data:(left, right) acc ->
        let%bind () = acc in
        unify_module_bindings ~signature:left ~definition:right >>| ignore)
  in
  return { signature with toplevel_type_constructors = type_constructors }
;;
