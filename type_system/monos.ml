open! Core
open! Shared
open! Frontend
open! Ty
open! Inference_state

let get_type_proof mono =
  match mono with
  | Named proof -> Some proof
  | _ -> None
;;

let get_ordering (type_name : Lowercase.t Qualified.t) =
  let open State.Result.Let_syntax in
  let%map _, _, { ordering; _ } = lookup_type_constructor type_name in
  Option.value ordering ~default:[]
;;

let rec show_type_proof { absolute_type_name; ordering; tyvar_map; _ } =
  let open State.Result.Let_syntax in
  let ordering = Option.value ordering ~default:[] in
  let%map type_var_map =
    List.map
      ~f:(fun k ->
        match Map.find tyvar_map k with
        | Some v -> show_mono v
        | None -> return k)
      ordering
    |> State.Result.all
  in
  let prefix_string =
    match type_var_map with
    | [] -> ""
    | [ x ] -> x ^ " "
    | l -> "(" ^ String.concat ~sep:", " l ^ ") "
  in
  let type_string = Qualified.show Fn.id absolute_type_name in
  prefix_string ^ type_string

and show_closed_monos { closure_mem_rep; _ } =
  State.Result.return ("{" ^ Mem_rep.show_abstract closure_mem_rep ^ "}")
(* let open State.Result.Let_syntax in *)
(* let%map list = *)
(*   List.fold closed ~init:(return []) ~f:(fun acc (_, mono) -> *)
(*     let%bind acc = acc in *)
(*     let%map s = show_mono mono in *)
(*     s :: acc) *)
(* in *)
(* "{" ^ String.concat ~sep:"|" list ^ "}" *)

and show_mono mono =
  let open State.Result.Let_syntax in
  match mono with
  | Weak (s, _) | TyVar (s, _) -> return s
  | Named proof -> show_type_proof proof
  | Function (a, b) | Closure (a, b, { closed_vars = []; _ }) ->
    let%bind a = show_mono_parenthized_functions a in
    let%map b = show_mono b in
    a ^ " -> " ^ b
  | Closure (a, b, closed) ->
    let%bind list = show_closed_monos closed in
    let%bind a = show_mono_parenthized_functions a in
    let%map b = show_mono b in
    a ^ [%string " -%{list}> "] ^ b
  | Tuple l ->
    let%map shown = List.map ~f:show_mono l |> State.Result.all in
    "(" ^ String.concat ~sep:", " shown ^ ")"
  | Reference m ->
    let%map m = show_mono m in
    "@" ^ m

and show_mono_parenthized_functions mono =
  let open State.Result.Let_syntax in
  let%map s = show_mono mono in
  match mono with
  | Function (_, _) | Closure (_, _, _) -> "(" ^ s ^ ")"
  | _ -> s
;;

let rec split_poly = function
  | Mono m -> Lowercase.Set.empty, m
  | Forall (a, b) ->
    let set, m = split_poly b in
    Set.add set a, m
;;

let split_poly_to_list poly =
  let rec inner = function
    | Mono m -> [], m
    | Forall (a, b) ->
      let l, m = inner b in
      a :: l, m
  in
  inner poly |> Tuple2.map_fst ~f:List.rev
;;

let show_mono_ufds (mono_ufds : Mono_ufds.t) =
  let open State.Result.Let_syntax in
  let%map alist =
    Map.to_alist mono_ufds
    |> List.map ~f:(fun (k, v) ->
      let%bind k = show_mono k in
      let%map v = show_mono v in
      k, v)
    |> State.Result.all
  in
  [%message (alist : (string * string) list)]
;;

let map_user_type_m user_type ~f =
  let open State.Result.Let_syntax in
  match user_type with
  | Abstract _ -> return user_type
  | Record l ->
    let%map l =
      State.Result.all
        (List.map l ~f:(fun (x, (y, mut)) ->
           let%map y = f y in
           x, (y, mut)))
    in
    Record l
  | Enum l ->
    let%map l =
      State.Result.all
        (List.map l ~f:(fun (x, y) ->
           let%map y =
             match y with
             | Some x -> f x >>| Option.some
             | None -> return None
           in
           x, y))
    in
    Enum l
  | User_mono mono ->
    let%map mono = f mono in
    User_mono mono
;;

let map_user_type user_type ~f =
  let f x = State.Result.return (f x) in
  map_user_type_m user_type ~f
;;

let rec mem_rep_of_mono = function
  | Weak (_, rep) -> rep
  | TyVar (_, rep) -> rep
  | Function _ -> Mem_rep.Closed `Reg
  | Closure (_, _, { closure_mem_rep; _ }) ->
    Mem_rep.Closed (`Struct [ Mem_rep.Closed `Reg; closure_mem_rep ])
  | Tuple l ->
    let list = List.map l ~f:mem_rep_of_mono in
    Mem_rep.Closed (`Struct list)
  | Reference _ -> Mem_rep.Closed `Reg
  | Named t -> t.mem_rep

and mem_rep_of_user_type = function
  | Abstract x -> x
  | Record l ->
    let list = List.map l ~f:(fun (_, (m, _)) -> mem_rep_of_mono m) in
    Mem_rep.Closed (`Struct list)
  | Enum l ->
    let list =
      List.map l ~f:(fun (_, m) ->
        Option.value_map m ~default:(Mem_rep.Closed `Bits0) ~f:mem_rep_of_mono)
    in
    Mem_rep.Closed (`Union list)
  | User_mono m -> mem_rep_of_mono m
;;

let rec map_ty_vars ~f (mono : mono) =
  match mono with
  | TyVar (a, b) -> Option.value (f (a, b)) ~default:mono
  | Weak _ -> mono
  | Closure (a, b, c) ->
    Closure (map_ty_vars ~f a, map_ty_vars ~f b, map_closed_monos ~f c)
  | Function (a, b) -> Function (map_ty_vars ~f a, map_ty_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_ty_vars ~f))
  | Named type_proof -> Named (map_type_proof ~f type_proof)
  | Reference x -> Reference (map_ty_vars ~f x)

and map_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  { type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_ty_vars ~f)
  }

and map_binding_alist ~f closed =
  List.map ~f:(fun (binding_id, mono) -> binding_id, map_ty_vars ~f mono) closed

and map_closed_monos
  ~f
  ({ closed_args; closed_vars; closure_mem_rep } : closure_info)
  =
  let closure_mem_rep =
    map_abstract_anys closure_mem_rep ~f:(fun s ->
      let mem_rep = Mem_rep.Any s in
      match f (s, mem_rep) with
      | None -> mem_rep
      | Some mono -> mem_rep_of_mono mono)
  in
  let closed_args = map_binding_alist ~f closed_args in
  let closed_vars = map_binding_alist ~f closed_vars in
  { closure_mem_rep; closed_args; closed_vars }
;;

let map_user_type_ty_vars ~f = map_user_type ~f:(map_ty_vars ~f)

let rec map_ty_vars_m ~f (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | TyVar (a, b) -> f (a, b)
  | Weak _ -> return mono
  | Closure (a, b, c) ->
    let%bind a = map_ty_vars_m ~f a in
    let%bind b = map_ty_vars_m ~f b in
    let%map c = map_closed_monos_m ~f c in
    Closure (a, b, c)
  | Function (a, b) ->
    let%bind a = map_ty_vars_m ~f a in
    let%map b = map_ty_vars_m ~f b in
    Function (a, b)
  | Tuple l ->
    let%map l = State.Result.all (List.map l ~f:(map_ty_vars_m ~f)) in
    Tuple l
  | Reference x ->
    let%map x = map_ty_vars_m ~f x in
    Reference x
  | Named type_proof ->
    let%map type_proof = map_type_proof_m ~f type_proof in
    Named type_proof

and map_type_proof_m ~f ({ tyvar_map; _ } as type_proof) =
  let open State.Result.Let_syntax in
  let%map tyvar_map =
    Map.fold
      tyvar_map
      ~init:(return Lowercase.Map.empty)
      ~f:(fun ~key ~data acc ->
        let%bind acc = acc in
        let%map data = map_ty_vars_m ~f data in
        Map.set acc ~key ~data)
  in
  { type_proof with tyvar_map }

and map_binding_alist_m ~f closed =
  State.Result.all
  @@ List.map
       ~f:(fun (binding_id, mono) ->
         let%map.State.Result mono = map_ty_vars_m ~f mono in
         binding_id, mono)
       closed

and map_closed_monos_m
  ~f
  ({ closed_args; closed_vars; closure_mem_rep } : closure_info)
  =
  let open State.Result.Let_syntax in
  let%bind closure_mem_rep =
    map_abstract_anys_m closure_mem_rep ~f:(fun s ->
      let mem_rep = Mem_rep.Any s in
      match%map.State f (s, mem_rep) with
      | Error _ -> Ok mem_rep
      | Ok mono -> Ok (mem_rep_of_mono mono))
  in
  let%bind closed_args = map_binding_alist_m ~f closed_args in
  let%map closed_vars = map_binding_alist_m ~f closed_vars in
  { closure_mem_rep; closed_args; closed_vars }
;;

let map_user_type_ty_vars_m ~f = map_user_type_m ~f:(map_ty_vars_m ~f)

let rec map_weak_vars ~f (mono : mono) =
  match mono with
  | Weak (a, b) -> Option.value (f (a, b)) ~default:mono
  | TyVar _ -> mono
  | Closure (a, b, c) ->
    Closure (map_weak_vars ~f a, map_weak_vars ~f b, map_weak_closed_monos ~f c)
  | Function (a, b) -> Function (map_weak_vars ~f a, map_weak_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_weak_vars ~f))
  | Reference x -> Reference (map_weak_vars ~f x)
  | Named type_proof -> Named (map_weak_type_proof ~f type_proof)

and map_weak_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  { type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_weak_vars ~f)
  }

and map_weak_binding_alist ~f closed =
  List.map
    ~f:(fun (binding_id, mono) -> binding_id, map_weak_vars ~f mono)
    closed

and map_weak_closed_monos
  ~f
  ({ closed_args; closed_vars; closure_mem_rep } : closure_info)
  =
  let closure_mem_rep =
    map_abstract_anys closure_mem_rep ~f:(fun s ->
      let mem_rep = Mem_rep.Any s in
      match f (s, mem_rep) with
      | None -> mem_rep
      | Some mono -> mem_rep_of_mono mono)
  in
  let closed_args = map_binding_alist ~f closed_args in
  let closed_vars = map_binding_alist ~f closed_vars in
  { closure_mem_rep; closed_args; closed_vars }
;;

let map_user_type_weak_vars ~f = map_user_type ~f:(map_weak_vars ~f)
let make_weak mono = map_ty_vars mono ~f:(fun (a, b) -> Some (Weak (a, b)))

let iter_ty_vars ~f mono =
  ignore
    (map_ty_vars mono ~f:(fun x ->
       f x;
       None))
;;

let iter_weak_vars ~f mono =
  ignore
    (map_weak_vars mono ~f:(fun x ->
       f x;
       None))
;;

let free_ty_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_ty_vars mono ~f:(fun (x, _) -> set := Set.add !set x);
  !set
;;

let free_ty_vars_list monos =
  let set = ref Lowercase.Set.empty in
  List.iter monos ~f:(fun mono ->
    iter_ty_vars mono ~f:(fun (x, _) -> set := Set.add !set x));
  !set
;;

let free_weak_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_weak_vars mono ~f:(fun (x, _) -> set := Set.add !set x);
  !set
;;

let replace_ty_vars ~replacement_map =
  map_ty_vars ~f:(fun (x, _) -> Map.find replacement_map x)
;;

let replace_ty_vars_type_proof ~replacement_map =
  map_type_proof ~f:(fun (x, _) -> Map.find replacement_map x)
;;

let no_free_vars poly =
  let set, mono = split_poly poly in
  let set' = free_ty_vars mono in
  Lowercase.Set.equal set set'
;;

let gen_replacement_map vars =
  let open State.Result.Let_syntax in
  let%bind replacements =
    State.Result.all
      (List.map vars ~f:(fun x ->
         let%bind.State sym = gensym in
         return (x, sym)))
  in
  match Lowercase.Map.of_alist replacements with
  | `Ok x -> return x
  | `Duplicate_key x ->
    State.Result.error [%message "duplicate key" (x : Lowercase.t)]
;;

let gen (mono : mono) : poly state_m =
  free_ty_vars mono
  |> Set.fold ~init:(Mono mono) ~f:(fun acc var -> Forall (var, acc))
  |> State.return
;;

let inst (poly : poly) : mono state_m =
  let open State.Let_syntax in
  let rec inner ~replacement_map poly =
    match poly with
    | Mono x -> return (replace_ty_vars ~replacement_map x)
    | Forall (a, poly) ->
      let%bind sym = gensym in
      let replacement_map =
        Map.set replacement_map ~key:a ~data:(TyVar (sym, Mem_rep.Any sym))
      in
      inner ~replacement_map poly
  in
  inner ~replacement_map:Lowercase.Map.empty poly
;;

let inst_result x = State.map (inst x) ~f:Result.return

let normalize (poly : poly) =
  let count = ref 0 in
  let get_var () =
    let i = !count mod 26 in
    let n = !count / 26 in
    incr count;
    let suff = if n = 0 then "" else Int.to_string n in
    let c = Char.of_int_exn (i + 97) in
    [%string "%{c#Char}%{suff}"]
  in
  let rec inner ~replacement_map poly =
    match poly with
    | Mono x -> Mono (replace_ty_vars ~replacement_map x)
    | Forall (a, poly) ->
      let rep = get_var () in
      let replacement_map =
        Map.set replacement_map ~key:a ~data:(TyVar (rep, Mem_rep.Any rep))
      in
      Forall (rep, inner ~replacement_map poly)
  in
  inner ~replacement_map:Lowercase.Map.empty poly
;;

let inst_type_proof type_proof =
  let open State.Result.Let_syntax in
  let%map replacement_map =
    Map.fold
      type_proof.tyvar_map
      ~init:(return Lowercase.Map.empty)
      ~f:(fun ~key ~data:_ acc ->
        let%bind acc = acc in
        let%map sym =
          match Map.find acc key with
          | Some x -> return x
          | None ->
            let%map res = State.map gensym ~f:Result.return in
            TyVar (res, Mem_rep.Any res)
        in
        Map.set acc ~key ~data:sym)
  in
  replace_ty_vars_type_proof ~replacement_map type_proof
;;

let split_poly_list l =
  let set, monos =
    List.fold l ~init:(Lowercase.Set.empty, []) ~f:(fun (set, monos) poly ->
      let new_vars, mono = split_poly poly in
      Set.union set new_vars, mono :: monos)
  in
  set, List.rev monos
;;

let inst_many poly_list =
  let open State.Let_syntax in
  let quantifiers, mono_list = split_poly_list poly_list in
  let%map replacement_map =
    Set.to_list quantifiers
    |> List.map ~f:(fun var ->
      let%map sym = gensym in
      var, TyVar (sym, Mem_rep.Any sym))
    |> State.all
    >>| Lowercase.Map.of_alist_exn
  in
  List.map mono_list ~f:(replace_ty_vars ~replacement_map)
;;

let inst_constructor constructor =
  let open State.Result.Let_syntax in
  let%bind arg, type_proof = lookup_constructor constructor in
  match arg with
  | None ->
    let%map type_proof = inst_type_proof type_proof in
    None, Named type_proof
  | Some poly_arg ->
    let%map mono_arg, mono_res =
      match%bind.State inst_many [ poly_arg; Mono (Named type_proof) ] with
      | [ mono_arg; mono_res ] -> return (mono_arg, mono_res)
      | _ ->
        State.Result.error [%message "inst_many returned wrong number of monos"]
    in
    Some mono_arg, mono_res
;;

let type_of_constructor constructor =
  let open State.Result.Let_syntax in
  match%map inst_constructor constructor with
  | None, mono -> mono
  | Some mono_arg, mono_res -> Function (mono_arg, mono_res)
;;

let make_free_vars_weak mono =
  let free_vars = free_ty_vars mono in
  let replacement_map =
    Set.to_map free_vars ~f:(fun x -> Weak (x, Mem_rep.Any x)) |> Obj.magic
  in
  replace_ty_vars ~replacement_map mono
;;

let poly_of_mono mono ~generalize ~value_restriction =
  match generalize, value_restriction with
  | false, _ -> State.Result.return @@ Mono mono
  | true, false -> State.map (gen mono) ~f:Result.return
  | true, true -> State.Result.return @@ Mono (make_weak mono)
;;

let apply_substs mono =
  let%map.State state = State.get in
  let mono =
    map_ty_vars mono ~f:(fun (a, b) ->
      let mono, _ = Mono_ufds.find state.mono_ufds (TyVar (a, b)) in
      Some mono)
  in
  Ok
    (map_weak_vars mono ~f:(fun (a, b) ->
       let mono, _ = Mono_ufds.find state.mono_ufds (Weak (a, b)) in
       Some mono))
;;

let lookup_in_type_proof mono ~look_for =
  let open State.Result.Let_syntax in
  match get_type_proof mono with
  | None -> State.Result.error [%message "can't find type proof" (mono : mono)]
  | Some { tyvar_map; _ } ->
    (match Map.find tyvar_map look_for with
     | Some x -> return x
     | None ->
       State.Result.error
         [%message
           "failed to find in type proof" (look_for : Lowercase.t) (mono : mono)])
;;

let rec mono_of_poly_no_inst poly =
  match poly with
  | Mono mono -> mono
  | Forall (_, r) -> mono_of_poly_no_inst r
;;

let gen_ty_var : _ state_result_m =
  let%map.State sym = gensym in
  Ok (TyVar (sym, Mem_rep.Any sym))
;;

let substitute (inner, mono) =
  let%map.State.Result mono = apply_substs mono in
  inner, mono
;;

let rec replace_type_name ~type_name (mono : mono) =
  match mono with
  | TyVar _ | Weak _ -> mono
  | Function (a, b) ->
    Function (replace_type_name ~type_name a, replace_type_name ~type_name b)
  | Closure (a, b, c) ->
    Closure (replace_type_name ~type_name a, replace_type_name ~type_name b, c)
  | Tuple l -> Tuple (List.map l ~f:(replace_type_name ~type_name))
  | Reference x -> Reference (replace_type_name ~type_name x)
  | Named type_proof -> Named (replace_type_name_proof ~type_name type_proof)

and replace_type_name_proof ~type_name type_proof =
  { type_proof with type_name }
;;

let rec show_mono_def (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | Named { type_id; _ } ->
    (match%bind lookup_type_map type_id with
     | _, _, { type_id = t'; _ } when phys_equal t' type_id -> show_mono mono
     | _, user_type, _ ->
       (match%bind show_user_type user_type with
        | Some s -> return s
        | None -> show_mono mono))
  | Weak (s, _) -> return [%string "weak %{s}"]
  | TyVar (s, _) -> return s
  | Closure _ | Function _ | Tuple _ | Reference _ -> show_mono mono

and show_user_type (user_type : user_type) =
  let open State.Result.Let_syntax in
  match user_type with
  | Abstract _ -> return None
  | Record fields ->
    [%sexp (fields : (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t)]
    |> Sexp.to_string_hum
    |> Option.some
    |> return
  | Enum cons ->
    let each (name, mono) =
      let%map mono_s =
        match mono with
        | Some mono ->
          let%map s = show_mono mono in
          " " ^ s
        | None -> return ""
      in
      [%string "\t| %{name}%{mono_s}"]
    in
    let%map l = State.Result.all @@ List.map cons ~f:each in
    "\n" ^ String.concat ~sep:"\n" l |> Option.some
  | User_mono mono -> show_mono_def mono >>| Option.some
;;

let rec show_module_bindings
  { toplevel_vars; toplevel_type_constructors; toplevel_modules; _ }
  =
  let open State.Result.Let_syntax in
  let%bind type_strings =
    Map.to_alist toplevel_type_constructors
    |> List.map ~f:(fun (type_name, type_id) ->
      let%bind args, user_type, _ = lookup_type_map type_id in
      let prefix_str =
        match args with
        | Some args -> show_type_constructor_arg args ^ " "
        | None -> ""
      in
      let%map rhs = show_user_type user_type in
      match rhs with
      | Some mono_s -> [%string "type %{prefix_str}%{type_name} = %{mono_s}"]
      | None -> [%string "type %{prefix_str}%{type_name}"])
    |> State.Result.all
  in
  let%bind var_strings =
    Map.to_alist toplevel_vars
    |> List.map ~f:(fun (v, poly_list) ->
      let%bind poly, _ =
        match poly_list with
        | x :: _ -> return x
        | _ -> State.Result.error [%message "Empty poly list"]
      in
      let poly = normalize poly in
      let _, mono = split_poly_to_list poly in
      let%map mono_s = show_mono mono in
      [%string "let %{v} : %{mono_s}"])
    |> State.Result.all
  in
  let%map module_bindings =
    Map.to_alist toplevel_modules
    |> List.map ~f:(fun (name, module_bindings) ->
      let%map module_s = show_module_bindings module_bindings in
      let module_s =
        String.split module_s ~on:'\n'
        |> List.map ~f:(fun s -> "    " ^ s)
        |> String.concat ~sep:"\n"
      in
      [%string "module %{name} = struct\n%{module_s}\nend"])
    |> State.Result.all
  in
  List.concat [ type_strings; var_strings; module_bindings ]
  |> String.concat ~sep:"\n\n"
;;
