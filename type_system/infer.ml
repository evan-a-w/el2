open! Core
open! Shared
open! Frontend
open! Ty

module Mono_ufds = Ufds.Make (struct
    type t = mono [@@deriving sexp, equal, hash, compare]
  end)

type module_history =
  { current_name : Uppercase.t
  ; previous_modules : (Uppercase.t * Typed_ast.module_) list
  }
[@@deriving sexp, equal, compare, fields]

type binding_state =
  { abstraction_level : int
  ; name : Lowercase.t
  ; poly : poly
  }
[@@deriving sexp, equal, compare, fields]

type state =
  { mono_ufds : Mono_ufds.t
  ; mem_rep_ufds : Mem_rep.Abstract_ufds.t
  ; current_module_binding : Typed_ast.module_
  ; current_path : Module_path.t
  ; local_vars :
      (poly * binding_id * bool (* rec binding *)) list Lowercase.Map.t
  ; module_history : module_history
  ; symbol_n : int
  ; abstraction_level : int
  ; binding_id_n : int
  ; binding_map : binding_state Binding_id.Map.t
  ; type_map : type_constructor Int.Map.t
  }
[@@deriving sexp, equal, compare, fields]

let on_mem_rep_ufds ~(f : ('a, Sexp.t, Mem_rep.Abstract_ufds.t) State.Result.t) =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let res, mem_rep_ufds = f state.mem_rep_ufds in
  match res with
  | Error e -> State.Result.error e
  | Ok res ->
    let%map () = State.Result.put { state with mem_rep_ufds } in
    res
;;

let lookup_binding_id binding_id =
  let%bind.State.Result state = State.Result.get in
  match Map.find state.binding_map binding_id with
  | Some x -> State.Result.return x
  | None -> State.Result.error [%message "Binding not found" (binding_id : int)]
;;

let add_module ~name ~module_bindings =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let current_module_binding = state.current_module_binding in
  let current_module_binding =
    { current_module_binding with
      toplevel_modules =
        Map.set
          current_module_binding.toplevel_modules
          ~key:name
          ~data:module_bindings
    }
  in
  State.Result.put { state with current_module_binding }
;;

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let get_binding_id =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let res = state.binding_id_n in
  let%map () = State.Result.put { state with binding_id_n = res + 1 } in
  res
;;

let get_abstraction_level =
  let open State.Result.Let_syntax in
  let%map state = State.Result.get in
  state.abstraction_level
;;

let incr_abstraction_level =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  State.Result.put
    { state with abstraction_level = state.abstraction_level + 1 }
;;

let decr_abstraction_level =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  State.Result.put
    { state with abstraction_level = state.abstraction_level - 1 }
;;

let add_type_constructor arg name user_type type_proof =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = arg, user_type, type_proof in
  let type_id = type_proof.type_id in
  let%bind type_map =
    match Map.add state.type_map ~key:type_id ~data with
    | `Ok m -> return m
    | `Duplicate ->
      State.Result.error
        [%message
          "Duplicate type constructor" (name : Lowercase.t) (type_id : int)]
  in
  match
    Map.add
      state.current_module_binding.toplevel_type_constructors
      ~key:name
      ~data:type_id
  with
  | `Ok m ->
    State.Result.put
      { state with
        type_map
      ; current_module_binding =
          { state.current_module_binding with toplevel_type_constructors = m }
      }
  | `Duplicate ->
    State.Result.error
      [%message "Duplicate type constructor" (name : Lowercase.t)]
;;

let set_type_constructor arg name user_type type_proof =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = arg, user_type, type_proof in
  let type_id = type_proof.type_id in
  let type_map = Map.set state.type_map ~key:type_id ~data in
  let toplevel_type_constructors =
    Map.set
      state.current_module_binding.toplevel_type_constructors
      ~key:name
      ~data:type_id
  in
  State.Result.put
    { state with
      type_map
    ; current_module_binding =
        { state.current_module_binding with toplevel_type_constructors }
    }
;;

let set_current_module_binding current_module_binding =
  State.Result.modify (fun state -> { state with current_module_binding })
;;

let get_current_module_binding =
  let%map.State.Result state = State.Result.get in
  state.current_module_binding
;;

let empty_module_bindings path = empty_module_bindings path Typed_ast.empty_data

let empty_state path =
  { mono_ufds = Mono_ufds.empty
  ; mem_rep_ufds = Mem_rep.Abstract_ufds.empty
  ; current_path = path
  ; current_module_binding = empty_module_bindings path
  ; module_history = { current_name = ""; previous_modules = [] }
  ; symbol_n = 0
  ; binding_id_n = 0
  ; local_vars = Lowercase.Map.empty
  ; type_map = base_type_map
  ; binding_map = Binding_id.Map.empty
  ; abstraction_level = 0
  }
;;

let gensym : string state_m =
  let open State.Let_syntax in
  let%bind state = State.get in
  let s = state.symbol_n in
  let%bind () = State.put { state with symbol_n = s + 1 } in
  let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
  let s = String.make 1 letter ^ Int.to_string (s / 26) in
  return s
;;

let print_ufds_map : unit state_result_m =
  let open State.Result.Let_syntax in
  let%map state = State.Result.get in
  print_s [%message (state.mono_ufds : Mono_ufds.t)]
;;

let add_type = add_type_constructor None

let add_module_var ?binding_id name poly =
  let open State.Result.Let_syntax in
  let%bind binding_id =
    match binding_id with
    | None -> get_binding_id
    | Some x -> return x
  in
  let%bind state = State.Result.get in
  let toplevel_vars =
    Map.add_multi
      state.current_module_binding.toplevel_vars
      ~key:name
      ~data:(poly, binding_id)
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  let binding_map =
    Map.set
      state.binding_map
      ~key:binding_id
      ~data:{ abstraction_level = state.abstraction_level; poly; name }
  in
  State.Result.put { state with current_module_binding; binding_map }
;;

let add_local_var ~is_rec ?binding_id name poly =
  let open State.Result.Let_syntax in
  let%bind binding_id =
    match binding_id with
    | None -> get_binding_id
    | Some x -> return x
  in
  let%bind state = State.Result.get in
  let local_vars =
    Map.add_multi state.local_vars ~key:name ~data:(poly, binding_id, is_rec)
  in
  let binding_map =
    Map.set
      state.binding_map
      ~key:binding_id
      ~data:{ abstraction_level = state.abstraction_level; poly; name }
  in
  State.Result.put { state with local_vars; binding_map }
;;

let pop_local_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let local_vars = Map.remove_multi state.local_vars name in
  State.Result.put { state with local_vars }
;;

let pop_module_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let toplevel_vars =
    Map.remove_multi state.current_module_binding.toplevel_vars name
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  State.Result.put { state with current_module_binding }
;;

let merge_variance_one variances ~name ~variance =
  Map.change variances name ~f:(function
    | None -> Some variance
    | Some x -> Some (Variance.merge x variance))
;;

let merge_variance_maps (variances1 : Variance.t Lowercase.Map.t) variances2 =
  Map.merge variances1 variances2 ~f:(fun ~key:_ -> function
    | `Left x | `Right x -> Some x
    | `Both (x, y) -> Some (Variance.merge x y))
;;

(* let rec type_constructor_variance_map = function *)
(*   | Single_arg (variance, name) -> Lowercase.Map.singleton name variance *)
(*   | Tuple_arg args -> *)
(*       List.fold args ~init:Lowercase.Map.empty ~f:(fun acc (variance, _) -> *)
(*           merge_variance_one acc variance) *)

let merge_variance_map_list =
  List.fold ~init:Lowercase.Map.empty ~f:merge_variance_maps
;;

(* let rec calculate_variance mono = *)
(*   match mono with *)
(*   | Abstract (_, Some arg) -> type_constructor_variance_map arg *)
(*   | Abstract _ | TyVar _ -> Lowercase.Map.empty *)
(*   | *)
(*   Tuple l -> *)
(*       List.fold l ~init:Lowercase.Map.empty ~f:(fun acc mono -> *)
(*           merge_variance_maps acc (calculate_variance mono)) *)
(*   | Reference mono -> calculate_variance mono *)
(*   | Closure (l, r) -> *)
(*       let left = *)
(*         match l with *)
(*         | TyVar x -> Lowercase.Map.singleton x Variance.Contravariant *)
(*         | _ -> Lowercase.Map.empty *)
(*       in *)
(*       let right = *)
(*         match r with *)
(*         | TyVar x -> Lowercase.Map.singleton x Variance.Covariant *)
(*         | _ -> Lowercase.Map.empty *)
(*       in *)
(*       merge_variance_maps left right *)
(*   | Record _ -> failwith "TODO" *)
(*   | Enum _ -> failwith "TODO" *)

let find mono : mono state_m =
  let%bind.State state = State.get in
  let mono, mono_ufds = Mono_ufds.find state.mono_ufds mono in
  let%map.State () = State.put { state with mono_ufds } in
  mono
;;

let union mono1 mono2 : unit state_m =
  let%bind.State state = State.get in
  let mono_ufds = Mono_ufds.union state.mono_ufds mono1 mono2 in
  State.put { state with mono_ufds }
;;

let ufds_find mono =
  let%map.State state = State.get in
  Mono_ufds.find state.mono_ufds mono
;;

let rec search_modules
  : type a.
    Typed_ast.module_
    -> qualifications:Qualified.qualifications
    -> search_for:(Typed_ast.module_ -> a option)
    -> a option
  =
  let find_in_opened_modules module_bindings ~qualifications ~search_for =
    List.find_map
      module_bindings.opened_modules
      ~f:(search_modules ~qualifications ~search_for)
  in
  fun module_bindings
      ~qualifications
      ~(search_for : Typed_ast.module_ -> a option) ->
    match qualifications with
    | [] ->
      (match search_for module_bindings with
       | Some x -> Some x
       | None ->
         find_in_opened_modules module_bindings ~qualifications ~search_for)
    | name :: qualifications ->
      let open Option.Let_syntax in
      let first =
        Map.find module_bindings.toplevel_modules name
        >>= search_modules ~qualifications ~search_for
      in
      (match first with
       | Some _ -> first
       | None ->
         find_in_opened_modules module_bindings ~qualifications ~search_for)
;;

let find_module_binding qualifications =
  let%bind.State state = State.get in
  match
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:Option.some
  with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "module not found" (qualifications : Qualified.qualifications)]
;;

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> snd @@ List.unzip l
  | Single_arg (_, x) -> [ x ]
;;

let ordering constructor_arg =
  Option.map constructor_arg ~f:constructor_arg_free_ty_vars
  |> Option.value ~default:[]
;;

let tyvar_map ordering =
  List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc tyvar ->
    Map.add_exn acc ~key:tyvar ~data:(TyVar (tyvar, Mem_rep.Any tyvar)))
;;

let lookup_type_map type_id =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match Map.find state.type_map type_id with
  | Some x -> State.Result.return x
  | None -> State.Result.error [%message "type not found" (type_id : int)]
;;

let lookup_type_constructor qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_type_constructors type_name)
  in
  match res with
  | Some type_id -> lookup_type_map type_id
  | None ->
    State.Result.error
      [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]
;;

let add_to_type_map ~type_id type_constructor =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match Map.add state.type_map ~key:type_id ~data:type_constructor with
  | `Ok type_map -> State.Result.put { state with type_map }
  | `Duplicate ->
    State.Result.error [%message "duplicate type id" (type_id : int)]
;;

let set_type_map ~type_id type_constructor =
  State.Result.modify (fun state ->
    let type_map = Map.set state.type_map ~key:type_id ~data:type_constructor in
    { state with type_map })
;;

let lookup_type ?(type_var = true) qualified_name =
  let open State.Result.Let_syntax in
  let qualifications, type_name = Qualified.split qualified_name in
  let type_var_fn = if type_var then Option.some else Fn.const None in
  let type_var_type =
    match qualifications with
    | [] -> type_var_fn (TyVar (type_name, Mem_rep.Any type_name))
    | _ -> None
  in
  let%bind res =
    match%map.State lookup_type_constructor qualified_name with
    | Ok (None, _, type_proof) -> Ok (Some (Named type_proof))
    | _ -> Ok None
  in
  match Option.first_some res type_var_type with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]
;;

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

and show_closed_monos closed =
  let open State.Result.Let_syntax in
  let%map list =
    List.fold closed ~init:(return []) ~f:(fun acc (_, mono) ->
      let%bind acc = acc in
      let%map s = show_mono mono in
      s :: acc)
  in
  "{" ^ String.concat ~sep:"|" list ^ "}"

and show_mono mono =
  let open State.Result.Let_syntax in
  match mono with
  | Weak (s, _) | TyVar (s, _) -> return s
  | Named proof -> show_type_proof proof
  | Function (a, b) ->
    let%bind a = show_mono a in
    let%map b = show_mono b in
    a ^ " -> " ^ b
  | Closure (a, b, closed) ->
    let%bind list = show_closed_monos closed in
    let%bind a = show_mono a in
    let%map b = show_mono b in
    a ^ [%string " -%{list}> "] ^ b
  | Tuple l ->
    let%map shown = List.map ~f:show_mono l |> State.Result.all in
    "(" ^ String.concat ~sep:", " shown ^ ")"
  | Reference m ->
    let%map m = show_mono m in
    "@" ^ m
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

let lookup_local_var name =
  let open State.Result.Let_syntax in
  let%map state = State.Result.get in
  match Map.find state.local_vars name with
  | Some (x :: _) -> Some x
  | _ -> None
;;

let lookup_var qualified_name : _ state_result_m =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  match qualifications, Map.find state.local_vars type_name with
  | [], Some (x :: _) -> State.Result.return x
  | _ ->
    let res =
      search_modules
        state.current_module_binding
        ~qualifications
        ~search_for:(fun module_bindings ->
          Map.find module_bindings.toplevel_vars type_name)
    in
    (match res with
     | Some ((a, b) :: _) -> State.Result.return (a, b, true)
     | None | Some [] ->
       State.Result.error
         [%message
           "var not in scope" (qualified_name : Lowercase.t Qualified.t)])
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

and map_closed_monos ~f closed =
  List.map ~f:(fun (binding_id, mono) -> binding_id, map_ty_vars ~f mono) closed
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

and map_closed_monos_m ~f closed =
  State.Result.all
  @@ List.map
       ~f:(fun (binding_id, mono) ->
         let%map.State.Result mono = map_ty_vars_m ~f mono in
         binding_id, mono)
       closed
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

and map_weak_closed_monos ~f closed =
  List.map
    ~f:(fun (binding_id, mono) -> binding_id, map_weak_vars ~f mono)
    closed
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

let rec type_of_type_expr type_expr : mono state_result_m =
  let open State.Result.Let_syntax in
  match type_expr with
  | Ast.Type_expr.Pointer type_expr ->
    let%map mono = type_of_type_expr type_expr in
    Reference mono
  | Ast.Type_expr.Tuple l ->
    let%map monos = State.Result.all (List.map l ~f:type_of_type_expr) in
    Tuple monos
  | Arrow (first, second) ->
    let%map first = type_of_type_expr first
    and second = type_of_type_expr second in
    Function (first, second)
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (first, second) ->
    let%bind constructor_arg, _, type_proof = lookup_type_constructor second in
    let%bind arg = type_of_type_expr first in
    let vars =
      match constructor_arg with
      | None -> []
      | Some (Single_arg (_, x)) -> [ x ]
      | Some (Tuple_arg l) -> List.unzip l |> snd
    in
    let arg_list =
      match arg with
      | Tuple l -> l
      | _ -> [ arg ]
    in
    let%bind zipped =
      match List.zip vars arg_list with
      | Ok x -> return x
      | Unequal_lengths ->
        State.Result.error
          [%message
            "type constructor expected more args"
              ~constructor:(second : string Qualified.t)
              ~got:(List.length arg_list : int)
              ~expected:(List.length vars : int)]
    in
    let%map replacement_map =
      match Lowercase.Map.of_alist zipped with
      | `Ok x -> return x
      | `Duplicate_key x ->
        State.Result.error
          [%message
            "duplicate arg in type constructor"
              ~constructor:(second : string Qualified.t)
              (x : Lowercase.t)]
    in
    Named (replace_ty_vars_type_proof ~replacement_map type_proof)
;;

let gen (mono : mono) : poly state_m =
  free_ty_vars mono
  |> Set.fold ~init:(Mono mono) ~f:(fun acc var -> Forall (var, acc))
  |> State.return
;;

let add_constructor name arg result =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match
    Map.add
      state.current_module_binding.toplevel_constructors
      ~key:name
      ~data:(arg, result)
  with
  | `Ok toplevel_constructors ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_constructors }
      }
  | `Duplicate ->
    State.Result.error
      [%message "duplicate constructor" ~constructor:(name : Uppercase.t)]
;;

let add_field field poly =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match
    Map.add state.current_module_binding.toplevel_fields ~key:field ~data:poly
  with
  | `Ok toplevel_fields ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_fields }
      }
  | `Duplicate ->
    State.Result.error [%message "duplicate field" ~field:(field : Lowercase.t)]
;;

let add_record field_map type_proof : _ state_result_m =
  let open State.Result.Let_syntax in
  let%bind field_set =
    Map.fold
      field_map
      ~init:(return Lowercase.Set.empty)
      ~f:(fun ~key ~data:(poly, mut) acc ->
        let%bind acc = acc in
        let%map () = add_field key (type_proof, mut, poly) in
        Set.add acc key)
  in
  let field_map = Lowercase.Map.map field_map ~f:fst in
  let%bind state = State.Result.get in
  match
    Map.add
      state.current_module_binding.toplevel_records
      ~key:field_set
      ~data:(field_map, type_proof)
  with
  | `Ok toplevel_records ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_records }
      }
  | `Duplicate ->
    State.Result.error
      [%message "duplicate record" (field_set : Lowercase.Set.t)]
;;

let lookup_record qualified_map =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, map = Qualified.split qualified_map in
  let fields =
    Map.fold map ~init:Lowercase.Set.empty ~f:(fun ~key ~data:_ acc ->
      Set.add acc key)
  in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_records fields)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "record not in scope" (fields : Lowercase.Set.t)]
;;

let lookup_constructor qualified_constructor =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_constructor in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_constructors name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "constructor not in scope" (name : Uppercase.t)]
;;

let lookup_field qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_name in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_fields name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error [%message "field not in scope" (name : Lowercase.t)]
;;

let type_proof_of_monos
  ~type_name
  ~absolute_type_name
  ~ordering
  monos
  type_id
  ~mem_rep
  =
  let free_var_set =
    List.fold monos ~init:Lowercase.Set.empty ~f:(fun acc mono ->
      Set.union acc (free_ty_vars mono))
  in
  let tyvar_map =
    Set.fold free_var_set ~init:Lowercase.Map.empty ~f:(fun acc x ->
      Map.add_exn acc ~key:x ~data:(TyVar (x, Mem_rep.Any x)))
  in
  { type_name; absolute_type_name; tyvar_map; ordering; type_id; mem_rep }
;;

let absolute_name ~state ~name =
  let rec inner curr l =
    match l with
    | [] -> curr
    | (u, _) :: rest -> inner (Qualified.Qualified (u, curr)) rest
  in
  let { current_name; previous_modules } = state.module_history in
  let init =
    match current_name with
    | "" -> Qualified.Unqualified name
    | _ -> Qualified.Qualified (current_name, Qualified.Unqualified name)
  in
  inner init previous_modules
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

let rec mem_rep_of_mono = function
  | Weak (_, rep) -> rep
  | TyVar (_, rep) -> rep
  | Function _ -> Mem_rep.Closed `Reg
  | Closure (_, _, rep) ->
    let list =
      List.map rep ~f:(fun (binding_id, mono) ->
        let m = mem_rep_of_mono mono in
        let name = Int.to_string binding_id in
        name, m)
    in
    Mem_rep.Closed (`Native_struct list)
  | Tuple l ->
    let list =
      List.mapi l ~f:(fun i x ->
        let m = mem_rep_of_mono x in
        [%string "_%{i#Int}"], m)
    in
    Mem_rep.Closed (`Native_struct list)
  | Reference m ->
    let m = mem_rep_of_mono m in
    Mem_rep.Closed (`Pointer m)
  | Named t -> t.mem_rep

and mem_rep_of_user_type = function
  | Abstract x -> x
  | Record l ->
    let list =
      List.map l ~f:(fun (a, (m, _)) ->
        let m = mem_rep_of_mono m in
        a, m)
    in
    Mem_rep.Closed (`Native_struct list)
  | Enum l ->
    let list =
      List.map l ~f:(fun (_, m) ->
        Option.value_map m ~default:(Mem_rep.Closed `Bits0) ~f:mem_rep_of_mono)
    in
    Mem_rep.Closed (`Union list)
  | User_mono m -> mem_rep_of_mono m
;;

let type_of_type_def_lit
  ~(type_name : string)
  ~type_id
  ~ordering
  (type_def_lit : Ast.Type_def_lit.t)
  =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let absolute_type_name = absolute_name ~state ~name:type_name in
  match type_def_lit with
  | Ast.Type_def_lit.Type_expr type_expr ->
    let%map mono = type_of_type_expr type_expr in
    let mem_rep = mem_rep_of_mono mono in
    let type_proof =
      { type_name
      ; absolute_type_name
      ; tyvar_map =
          free_ty_vars mono
          |> Set.fold ~init:Lowercase.Map.empty ~f:(fun acc x ->
            Map.add_exn ~key:x ~data:(TyVar (x, Mem_rep.Any x)) acc)
      ; ordering
      ; type_id
      ; mem_rep
      }
    in
    type_proof, User_mono mono
  | Ast.Type_def_lit.Record l ->
    let%bind record_type =
      List.map l ~f:(fun (name, (type_expr, mutability)) ->
        let%map mono = type_of_type_expr type_expr in
        name, (mono, mutability))
      |> State.Result.all
    in
    let mem_rep = mem_rep_of_user_type (Record record_type) in
    let type_proof =
      type_proof_of_monos
        ~type_name
        ~absolute_type_name
        ~ordering
        ~mem_rep
        (List.map record_type ~f:(Fn.compose fst snd))
        type_id
    in
    let user_type = Record record_type in
    let%bind polys =
      State.Result.all
        (List.map record_type ~f:(fun (field, (mono, mut)) ->
           let%map.State poly = gen mono in
           Ok (field, (poly, mut))))
    in
    let field_map = Lowercase.Map.of_alist_exn polys in
    let%map () = add_record field_map type_proof in
    type_proof, user_type
  | Ast.Type_def_lit.Enum l ->
    let%bind enum_type =
      List.map l ~f:(fun (name, type_expr) ->
        let%map mono =
          match type_expr with
          | Some type_expr -> type_of_type_expr type_expr >>| Option.some
          | None -> return None
        in
        name, mono)
      |> State.Result.all
    in
    let mem_rep = mem_rep_of_user_type (Enum enum_type) in
    let monos = List.filter_map enum_type ~f:(fun (_, mono) -> mono) in
    let type_proof =
      type_proof_of_monos
        ~type_name
        ~absolute_type_name
        ~ordering
        monos
        type_id
        ~mem_rep
    in
    let user_type = Enum enum_type in
    let%map () =
      State.Result.all_unit
      @@ List.map enum_type ~f:(fun (x, mono_option) ->
        let%bind poly_option =
          match mono_option with
          | Some mono -> State.map (gen mono) ~f:(fun x -> Ok (Some x))
          | None -> return None
        in
        add_constructor x poly_option type_proof)
    in
    type_proof, user_type
;;

let set_ordering (mono : mono) ~ordering =
  match mono with
  | Named p -> Named { p with ordering = Some ordering }
  | _ -> mono
;;

let type_type_def
  ({ type_name = type_binding; type_def; ast_tags = _ } :
    Ast.Type_def_lit.t Ast.type_description)
  =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match type_binding with
  | Ast.Type_binding.Mono type_name ->
    let absolute_type_name = absolute_name ~state ~name:type_name in
    let type_id = type_id_of_absolute_name absolute_type_name in
    let%bind type_proof, user_type =
      type_of_type_def_lit ~type_name ~type_id ~ordering:None type_def
    in
    let%map () =
      match Map.length type_proof.tyvar_map with
      | 0 -> add_type type_name user_type type_proof
      | _ ->
        State.Result.error
          [%message
            "type definition has free type variables"
              (user_type : user_type)
              ~vars:
                (Map.to_alist type_proof.tyvar_map |> List.map ~f:fst
                  : Lowercase.t list)
              (type_name : Lowercase.t)]
    in
    Typed_ast.(
      Type_def Type_def.{ type_binding; type_def = user_type; type_proof })
  | Ast.Type_binding.Poly (arg, type_name) ->
    let absolute_type_name = absolute_name ~state ~name:type_name in
    let type_id = type_id_of_absolute_name absolute_type_name in
    let constructor_arg =
      match arg with
      | Ast.Type_binding.Single (v, l) -> Some (Single_arg (v, l))
      | Ast.Type_binding.Tuple l -> Some (Tuple_arg l)
    in
    let ordering = ordering constructor_arg in
    let lhs_ty_vars =
      List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc key ->
        Map.add_exn acc ~key ~data:(TyVar (key, Mem_rep.Any key)))
    in
    let mem_rep = Mem_rep.Any "0" in
    let type_proof =
      { type_name
      ; absolute_type_name
      ; ordering = Some ordering
      ; type_id
      ; tyvar_map = lhs_ty_vars
      ; mem_rep
      }
    in
    let%bind () =
      add_type_constructor
        constructor_arg
        type_name
        (Abstract mem_rep)
        type_proof
    in
    let%bind type_proof', user_type =
      type_of_type_def_lit
        ~type_name
        ~type_id
        ~ordering:(Some ordering)
        type_def
    in
    let rhs_ty_vars = Map.key_set type_proof'.tyvar_map |> Obj.magic in
    let lhs_ty_vars = Map.key_set lhs_ty_vars |> Obj.magic in
    let%map () =
      match Lowercase.Set.equal lhs_ty_vars rhs_ty_vars with
      | true ->
        set_type_constructor constructor_arg type_name user_type type_proof
      | false ->
        State.Result.error
          [%message
            "Type vars not equal in type def"
              (type_name : Lowercase.t)
              (type_proof : type_proof)
              (lhs_ty_vars : Lowercase.Set.t)
              (rhs_ty_vars : Lowercase.Set.t)]
    in
    Typed_ast.(
      Type_def Type_def.{ type_binding; type_def = user_type; type_proof })
;;

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

let unification_error mono1 mono2 =
  let%bind.State.Result a = show_mono mono1 in
  let%bind.State.Result b = show_mono mono2 in
  State.Result.error
    [%message "failed to unify types" ~_:(a : string) ~_:(b : string)]
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

let unify_mem_rep m1 m2 =
  let open State.Result.Let_syntax in
  let%bind m1 = on_mem_rep_ufds ~f:(Mem_rep.find m1) in
  let%bind m2 = on_mem_rep_ufds ~f:(Mem_rep.find m2) in
  on_mem_rep_ufds ~f:(Mem_rep.unify m1 m2)
;;

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
  | Closure (x1, x2, m1), Closure (y1, y2, m2) ->
    let%bind () = unify x1 y1 in
    let%bind () = unify x2 y2 in
    let error () =
      let%bind m1 = show_closed_monos m1 in
      let%bind m2 = show_closed_monos m2 in
      State.Result.error [%message "closure mismatch" m1 m2]
    in
    (match List.zip m1 m2 with
     | Unequal_lengths -> error ()
     | Ok l ->
       State.Result.all_unit
       @@ List.map l ~f:(fun ((_, m1), (_, m2)) ->
         let m1 = mem_rep_of_mono m1 in
         let m2 = mem_rep_of_mono m2 in
         unify_mem_rep m1 m2))
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
  | Closure (x1, x2, _), Closure (y1, y2, _) ->
    let%bind () = unify_less_general x1 y1 in
    unify_less_general x2 y2
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

let open_module (qualifications : Qualified.qualifications) =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let%bind module_bindings = find_module_binding qualifications in
  let current_module_binding =
    { current_module_binding with
      opened_modules = module_bindings :: current_module_binding.opened_modules
    }
  in
  State.Result.put { state with current_module_binding }
;;

let pop_opened_module =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let opened_modules =
    match current_module_binding.opened_modules with
    | [] -> []
    | _ :: xs -> xs
  in
  let current_module_binding = { current_module_binding with opened_modules } in
  State.Result.put { state with current_module_binding }
;;

let change_to_module name module_bindings =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding = old_module_binding; _ } as state) =
    State.Result.get
  in
  let { current_name; previous_modules } = state.module_history in
  let module_history =
    { current_name = name
    ; previous_modules = (current_name, old_module_binding) :: previous_modules
    }
  in
  let current_module_binding =
    { module_bindings with
      opened_modules = old_module_binding :: old_module_binding.opened_modules
    }
  in
  State.Result.put
    { state with
      current_module_binding
    ; module_history
    ; current_path = module_bindings.path
    }
;;

let change_to_new_module name =
  let%bind.State.Result state = State.Result.get in
  change_to_module
    name
    (empty_module_bindings (Module_path.append state.current_path name))
;;

let pop_module : (string * Typed_ast.module_) state_result_m =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let old_module_binding = state.current_module_binding in
  let { current_name; previous_modules } = state.module_history in
  let current_module_binding, module_history, current_path =
    match previous_modules with
    | [] ->
      ( empty_module_bindings state.current_path
      , { current_name; previous_modules = [] }
      , state.current_path )
    | (name, current_module_binding) :: xs ->
      ( current_module_binding
      , { current_name = name; previous_modules = xs }
      , Module_path.pop state.current_path )
  in
  let%map () =
    State.Result.put
      { state with current_module_binding; module_history; current_path }
  in
  current_name, old_module_binding
;;

let pop_module_and_add ~module_bindings =
  let%bind.State.Result current_name, _ = pop_module in
  add_module ~name:current_name ~module_bindings
;;

let pop_module_and_add_current =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  pop_module_and_add ~module_bindings:state.current_module_binding
;;

let make_free_vars_weak mono =
  let free_vars = free_ty_vars mono in
  let replacement_map =
    Set.to_map free_vars ~f:(fun x -> Weak (x, Mem_rep.Any x)) |> Obj.magic
  in
  replace_ty_vars ~replacement_map mono
;;

let rec value_restriction expr =
  match expr with
  | Ast.Lambda _ -> false
  | Ast.Node n -> value_restriction_node n
  | Ast.If (a, b, c) -> List.exists ~f:value_restriction [ a; b; c ]
  | Ast.App (_, _) -> true
  | Ast.Let_in (Ast.Nonrec (_, b), c) ->
    List.exists ~f:value_restriction [ b; c ]
  | Ast.Let_in (Ast.Rec l, c) ->
    List.exists ~f:value_restriction (c :: List.map l ~f:snd)
  | Ast.Match (_, _) -> true
  | Ast.Typed (e, _) -> value_restriction e
  | _ -> true

and value_restriction_node node =
  match node with
  | Ast.Var _ -> false
  | Ast.Literal _ -> false
  | Ast.Tuple qualified ->
    let _, l = Qualified.split qualified in
    List.exists ~f:value_restriction l
  | Ast.Constructor _ -> true
  | Ast.Record qualified ->
    let _, l = Qualified.split qualified in
    Map.exists ~f:value_restriction l
  | Ast.Wrapped qualified ->
    let _, l = Qualified.split qualified in
    value_restriction l
;;

let gen_ty_var : _ state_result_m =
  let%map.State sym = gensym in
  Ok (TyVar (sym, Mem_rep.Any sym))
;;

let type_literal literal =
  State.Result.return @@ Typed_ast.expr_of_literal literal
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

exception Field_left_only of string
exception Field_right_only of string

type add_var_t = ?binding_id:type_id -> string -> poly -> unit state_result_m

let rec gen_binding_ty_vars
  ~initial_vars
  ~(binding : Ast.Binding.t)
  ~(add_var : add_var_t)
  : (mono * Lowercase.t list) state_result_m
  =
  let open State.Result.Let_syntax in
  match binding with
  | Ast.Binding.Literal l ->
    let mono = Typed_ast.Literal.mono_of_t l in
    return (mono, initial_vars)
  | Ast.Binding.Name var ->
    let%bind ty_var = gen_ty_var in
    let poly = Mono ty_var in
    let%map () = add_var var poly in
    ty_var, var :: initial_vars
  | Ast.Binding.Constructor (constructor, rest) ->
    let%bind mono_arg, mono_res = inst_constructor constructor in
    (match rest, mono_arg with
     | None, None -> return (mono_res, [])
     | None, Some mono_arg ->
       State.Result.error
         [%message
           "Constructor takes an argument (none given)"
             (constructor : Uppercase.t Qualified.t)
             (mono_arg : mono)]
     | Some given, None ->
       State.Result.error
         [%message "Constructor takes no argument" (given : Ast.Binding.t)]
     | Some binding, Some mono_arg ->
       let%bind mono, vars =
         gen_binding_ty_vars ~initial_vars ~binding ~add_var
       in
       let%map () = unify mono_arg mono in
       mono_res, vars)
  | Ast.Binding.Typed (binding, value_tag) ->
    let type_expr = value_tag.Ast.Value_tag.type_expr in
    (match type_expr with
     | None -> gen_binding_ty_vars ~initial_vars ~binding ~add_var
     | Some type_expr ->
       let%bind tagged_mono = type_of_type_expr type_expr in
       let%bind mono, vars =
         gen_binding_ty_vars ~initial_vars ~binding ~add_var
       in
       let%map () = unify tagged_mono mono in
       mono, vars)
  | Ast.Binding.Pointer binding ->
    let%map mono, vars = gen_binding_ty_vars ~initial_vars ~binding ~add_var in
    Reference mono, vars
  | Ast.Binding.Renamed (binding, var) ->
    let%bind mono, vars = gen_binding_ty_vars ~initial_vars ~binding ~add_var in
    let%map () = add_var var (Mono mono) in
    mono, var :: vars
  | Ast.Binding.Tuple qualified ->
    let qualifications, tuple = Qualified.split qualified in
    let%bind () = open_module qualifications in
    let%bind processed_list =
      State.Result.all
        (List.map tuple ~f:(fun binding ->
           gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var))
    in
    let monos, vars_list = List.unzip processed_list in
    let vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    Tuple monos, List.concat [ vars; initial_vars ]
  | Ast.Binding.Record qualified_map ->
    let qualifications, record = Qualified.split qualified_map in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof = lookup_record qualified_map in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_searched = Named type_proof in
    let%bind field_map =
      try
        return
        @@ Map.merge record field_map ~f:(fun ~key -> function
          | `Both x -> Some x
          | `Left _ -> raise (Field_left_only key)
          | `Right _ -> raise (Field_right_only key))
      with
      | Field_left_only key ->
        State.Result.error
          [%message
            "Field in pattern is not present in type" (key : Lowercase.t)]
      | Field_right_only key ->
        State.Result.error
          [%message "Field is not present in pattern" (key : Lowercase.t)]
    in
    let%bind vars_list =
      Map.fold
        field_map
        ~init:(State.Result.return [])
        ~f:(fun ~key:_ ~data:(binding, poly) acc ->
          let%bind vars_list = acc in
          let mono = mono_of_poly_no_inst poly in
          let%bind mono =
            map_ty_vars_m mono ~f:(fun (v, _) ->
              lookup_in_type_proof mono_searched ~look_for:v)
          in
          let%bind mono', vars =
            gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var
          in
          let%map () = unify mono mono' in
          vars :: vars_list)
    in
    let res_vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    mono_searched, List.concat [ res_vars; initial_vars ]
;;

let gen_var var ~(add_var : add_var_t) ~pop_var =
  let open State.Result.Let_syntax in
  let%bind value, binding_id, _ = lookup_var (Qualified.Unqualified var) in
  let%bind () = pop_var var in
  let%bind mono = inst_result value in
  let%bind mono = apply_substs mono in
  let%bind poly = State.Result.t_of_state (gen mono) in
  add_var ~binding_id var poly
;;

let is_plain_function poly =
  let mono = mono_of_poly_no_inst poly in
  match%map.State.Result reach_end_mono mono with
  | Function (_, _) -> true
  | Weak _ | TyVar _ | Tuple _ | Reference _ | Named _ | Closure (_, _, _) ->
    false
;;

let rec already_bound
  ?(acc = [])
  ?(shadowed = Lowercase.Set.empty)
  (expr : Ast.expr)
  =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node n -> already_bound_node ~acc ~shadowed n
  | Ast.If (a, b, c) ->
    let%bind acc = already_bound ~acc ~shadowed a in
    let%bind acc = already_bound ~acc ~shadowed b in
    already_bound ~acc ~shadowed c
  | Ast.Lambda (binding, expr) ->
    let shadowed = add_shadowed ~shadowed ~binding in
    already_bound ~acc ~shadowed expr
  | Ast.App (a, b) ->
    let%bind acc = already_bound ~acc ~shadowed a in
    already_bound ~acc ~shadowed b
  | Ast.Let_in (Nonrec (binding, expr1), expr2) ->
    let%bind acc = already_bound ~acc ~shadowed expr1 in
    let shadowed = add_shadowed ~shadowed ~binding in
    already_bound ~acc ~shadowed expr2
  | Ast.Let_in (Rec l, expr2) ->
    let%bind shadowed =
      List.fold l ~init:(return shadowed) ~f:(fun acc (binding, _) ->
        let%map shadowed = acc in
        add_shadowed ~shadowed ~binding)
    in
    let%bind acc =
      List.fold l ~init:(return acc) ~f:(fun acc (_, expr) ->
        let%bind acc = acc in
        already_bound ~acc ~shadowed expr)
    in
    already_bound ~acc ~shadowed expr2
  | Ast.Ref expr
  | Ast.Typed (expr, _)
  | Ast.Deref expr
  | Ast.Field_access (expr, _) -> already_bound ~acc ~shadowed expr
  | Ast.Field_set (expr1, _, expr2) ->
    let%bind acc = already_bound ~acc ~shadowed expr1 in
    already_bound ~acc ~shadowed expr2
  | Ast.Match (expr, cases) ->
    let%bind acc = already_bound ~acc ~shadowed expr in
    List.fold
      cases
      ~init:(State.Result.return acc)
      ~f:(fun acc (binding, expr) ->
        let%bind acc = acc in
        let shadowed = add_shadowed ~shadowed ~binding in
        already_bound ~acc ~shadowed expr)

and already_bound_node ~acc ~shadowed (node : Ast.node) =
  let open State.Result.Let_syntax in
  match node with
  | Ast.Var (Qualified.Unqualified s) ->
    let is_shadowed = Set.mem shadowed s in
    (match%bind lookup_local_var s with
     | Some (poly, binding_id, false) when not is_shadowed ->
       (match%map is_plain_function poly with
        | true -> acc
        | false -> binding_id :: acc)
     | _ -> return acc)
  | Ast.Var _ | Ast.Literal _ | Ast.Constructor _ -> return acc
  | Ast.Tuple l ->
    let l = Qualified.inner l in
    List.fold l ~init:(return acc) ~f:(fun acc expr ->
      let%bind acc = acc in
      already_bound ~acc ~shadowed expr)
  | Ast.Record r ->
    let r = Qualified.inner r in
    Map.fold r ~init:(return acc) ~f:(fun ~key:_ ~data:expr acc ->
      let%bind acc = acc in
      already_bound ~acc ~shadowed expr)
  | Ast.Wrapped e ->
    let e = Qualified.inner e in
    already_bound ~acc ~shadowed e

and add_shadowed ~shadowed ~binding =
  let res = ref shadowed in
  Ast.Binding.iter_names ~f:(fun name -> res := Set.add !res name) binding;
  !res
;;

let rec type_node node =
  let open State.Result.Let_syntax in
  match node with
  | Ast.Literal literal -> type_literal literal
  | Ast.Var var_name ->
    let%bind poly, binding_id, _ = lookup_var var_name in
    let%map mono = inst_result poly in
    Typed_ast.(Node (Var (var_name, binding_id))), mono
  | Ast.Tuple qualified_tuple ->
    let qualifications, tuple = Qualified.split qualified_tuple in
    let%bind () = open_module qualifications in
    let%bind l = State.Result.all (List.map tuple ~f:type_expr) in
    let monos = List.map l ~f:snd in
    let%map () = pop_opened_module in
    let l = Qualified.prepend ~qualifications (Unqualified l) in
    Typed_ast.(Node (Tuple l)), Tuple monos
  | Ast.Wrapped qualified_expr ->
    let qualifications, expr = Qualified.split qualified_expr in
    let%bind () = open_module qualifications in
    let%bind ((_, mono) as expr) = type_expr expr in
    let%map () = pop_opened_module in
    let expr = Qualified.prepend ~qualifications (Unqualified expr) in
    Typed_ast.(Node (Wrapped expr)), mono
  | Ast.Constructor constructor ->
    let%map mono = type_of_constructor constructor in
    Typed_ast.(Node (Constructor constructor)), mono
  | Ast.Record qualified_record ->
    let qualifications, record = Qualified.split qualified_record in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof =
      lookup_record (Qualified.Unqualified record)
    in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_res = Named type_proof in
    let field_list = Map.to_alist field_map in
    (* lookup the tyvar in the map thingo in mono_res *)
    let%bind field_mono_map =
      List.map field_list ~f:(fun (field, poly) ->
        let mono = mono_of_poly_no_inst poly in
        let%map mono =
          map_ty_vars_m mono ~f:(fun (v, _) ->
            lookup_in_type_proof mono_res ~look_for:v)
        in
        field, mono)
      |> State.Result.all
      >>| Lowercase.Map.of_alist_exn
    in
    let%bind expr_map =
      Map.fold
        record
        ~init:(State.Result.return Lowercase.Map.empty)
        ~f:(fun ~key:field ~data:expr acc ->
          let%bind acc = acc in
          let%bind ((_, mono) as expr) = type_expr expr in
          let%map () =
            match Map.find field_mono_map field with
            | None ->
              State.Result.error
                [%message "Unknown field" (field : Lowercase.t)]
            | Some field_mono -> unify field_mono mono
          in
          Map.set acc ~key:field ~data:expr)
    in
    let expr_map = Qualified.prepend ~qualifications (Unqualified expr_map) in
    let%map mono = apply_substs mono_res in
    Typed_ast.(Node (Record expr_map)), mono

and add_module_var_mono ~generalize ~value_restriction var mono =
  let open State.Result.Let_syntax in
  let%bind poly = poly_of_mono ~generalize ~value_restriction mono in
  add_module_var var poly

and add_local_var_mono ~is_rec ~generalize ~value_restriction var mono =
  let open State.Result.Let_syntax in
  let%bind poly = poly_of_mono ~generalize ~value_restriction mono in
  add_local_var ~is_rec var poly

and type_binding ~act_on_var ~initial_vars ~(binding : Ast.Binding.t) ~mono =
  let open State.Result.Let_syntax in
  match binding with
  | Ast.Binding.Literal l ->
    let%bind _, binding_mono = type_literal l in
    let%map () = unify binding_mono mono in
    Typed_ast.Literal_binding l, mono, initial_vars
  | Ast.Binding.Name var ->
    (* let%bind poly = poly_of_mono ~generalize ~value_restriction mono in *)
    (* let%map () = act_on_var var poly in *)
    let%map () = act_on_var var mono in
    Typed_ast.Name_binding var, mono, var :: initial_vars
  | Ast.Binding.Constructor (constructor, rest) ->
    let%bind mono_arg, mono_res = inst_constructor constructor in
    (match rest, mono_arg with
     | None, None ->
       return (Typed_ast.Constructor_binding (constructor, None), mono_res, [])
     | None, Some mono_arg ->
       State.Result.error
         [%message
           "Constructor takes an argument (none given)"
             (constructor : Uppercase.t Qualified.t)
             (mono_arg : mono)]
     | Some given, None ->
       State.Result.error
         [%message
           "Constructor takes no argument"
             (constructor : Uppercase.t Qualified.t)
             (given : Ast.Binding.t)]
     | Some binding, Some mono_arg ->
       let%bind inner, _, vars =
         type_binding ~act_on_var ~initial_vars ~binding ~mono:mono_arg
       in
       let%map () = unify mono_res mono in
       Typed_ast.Constructor_binding (constructor, Some inner), mono_res, vars)
  | Ast.Binding.Typed (binding, value_tag) ->
    let type_expr = value_tag.Ast.Value_tag.type_expr in
    (match type_expr with
     | None -> type_binding ~act_on_var ~initial_vars ~binding ~mono
     | Some type_expr ->
       let%bind tagged_mono = type_of_type_expr type_expr in
       let%bind () = unify tagged_mono mono in
       let%bind res, mono_res, vars =
         type_binding ~act_on_var ~initial_vars ~binding ~mono
       in
       let%map () = unify mono_res tagged_mono in
       res, mono, vars)
  | Ast.Binding.Renamed (binding, var) ->
    let%bind res, mono, vars =
      type_binding ~act_on_var ~initial_vars ~binding ~mono
    in
    let%map () = act_on_var var mono in
    Typed_ast.Renamed_binding (res, var), mono, var :: vars
  | Ast.Binding.Pointer binding ->
    let%bind ty_var = gen_ty_var in
    let%bind () = unify (Reference ty_var) mono in
    let%map inner, mono, vars =
      type_binding ~act_on_var ~initial_vars ~binding ~mono:ty_var
    in
    Typed_ast.Reference_binding inner, mono, vars
  | Ast.Binding.Tuple qualified ->
    let qualifications, tuple = Qualified.split qualified in
    let%bind () = open_module qualifications in
    let%bind arg_monos =
      match mono with
      | Tuple list ->
        if List.length list <> List.length tuple
        then
          State.Result.error
            [%message
              "Tuple length mismatch" (mono : mono) (tuple : Ast.Binding.t list)]
        else State.Result.return list
      | _ -> State.Result.error [%message "Expected tuple" (mono : mono)]
    in
    let tuple_zipped = List.zip_exn tuple arg_monos in
    let%bind processed_list =
      State.Result.all
        (List.map tuple_zipped ~f:(fun (binding, mono) ->
           type_binding ~act_on_var ~initial_vars:[] ~binding ~mono))
    in
    let bindings, monos, vars_list = List.unzip3 processed_list in
    let bindings = Qualified.prepend ~qualifications (Unqualified bindings) in
    let vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    ( Typed_ast.Tuple_binding bindings
    , Tuple monos
    , List.concat [ vars; initial_vars ] )
  | Ast.Binding.Record qualified_map ->
    let qualifications, record = Qualified.split qualified_map in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof = lookup_record qualified_map in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_searched = Named type_proof in
    let%bind () = unify mono_searched mono in
    let%bind field_map =
      try
        return
        @@ Map.merge record field_map ~f:(fun ~key -> function
          | `Both x -> Some x
          | `Left _ -> raise (Field_left_only key)
          | `Right _ -> raise (Field_right_only key))
      with
      | Field_left_only key ->
        State.Result.error
          [%message
            "Field in pattern is not present in type" (key : Lowercase.t)]
      | Field_right_only key ->
        State.Result.error
          [%message "Field is not present in pattern" (key : Lowercase.t)]
    in
    let%bind inner_map, vars_list =
      Map.fold
        field_map
        ~init:(State.Result.return (Lowercase.Map.empty, []))
        ~f:(fun ~key ~data:(binding, poly) acc ->
          let%bind inner_map, vars_list = acc in
          let mono = mono_of_poly_no_inst poly in
          let%bind mono =
            map_ty_vars_m mono ~f:(fun (v, _) ->
              lookup_in_type_proof mono_searched ~look_for:v)
          in
          let%bind inner, mono', vars =
            type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
          in
          let%map () = unify mono' mono in
          let inner_map = Map.set inner_map ~key ~data:inner in
          inner_map, vars :: vars_list)
    in
    let inner_map = Qualified.prepend ~qualifications (Unqualified inner_map) in
    let res_vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    ( Typed_ast.Record_binding inner_map
    , mono_searched
    , List.concat [ res_vars; initial_vars ] )

and let_each_of_binding_typed
  ~(binding : Ast.Binding.t)
  ~mono1
  ~expr2
  ~generalize
  ~value_restriction
  ~add_var_mono
  ~pop_var
  =
  let open State.Result.Let_syntax in
  let act_on_var = add_var_mono ~generalize ~value_restriction in
  let%bind binding, mono, vars =
    type_binding ~act_on_var ~initial_vars:[] ~binding ~mono:mono1
  in
  let%bind () = unify mono mono1 in
  let%bind res = type_expr expr2 in
  let%map () = State.Result.all_unit (List.map vars ~f:pop_var) in
  binding, res

and mono_of_binding
  ~(binding : Ast.Binding.t)
  ~expr1
  ~expr2
  ~generalize
  ~add_var_mono
  ~pop_var
  =
  let open State.Result.Let_syntax in
  let value_restriction = value_restriction expr1 in
  let%bind inner, mono1 = type_expr expr1 in
  let%bind mono1 = apply_substs mono1 in
  let%map binding, mono =
    let_each_of_binding_typed
      ~binding
      ~mono1
      ~expr2
      ~generalize
      ~value_restriction
      ~add_var_mono
      ~pop_var
  in
  binding, (inner, mono)

and add_nonrec_bindings ~binding ~expr ~add_var_mono =
  let open State.Result.Let_syntax in
  let value_restriction = value_restriction expr in
  let%bind inner, mono = type_expr expr in
  let%bind mono = apply_substs mono in
  let act_on_var = add_var_mono ~generalize:true ~value_restriction in
  let%bind binding, mono', vars =
    type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
  in
  let%map () = unify mono mono' in
  binding, (inner, mono), vars

and check_rec_rhs expr =
  match expr with
  | Ast.Lambda _ -> State.Result.return ()
  | _ ->
    State.Result.error
      [%message
        "Only functions are allowed in rec bindings" ~got:(expr : Ast.expr)]

and add_rec_bindings l ~(add_var : add_var_t) ~pop_var =
  let open State.Result.Let_syntax in
  let%bind () = incr_abstraction_level in
  let%bind bindings =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
         let%bind () = check_rec_rhs expr in
         let%map _, b =
           gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var
         in
         b, value_restriction expr))
  in
  let%bind () = decr_abstraction_level in
  let act_on_var var mono =
    let%bind current, _, _ = lookup_var (Qualified.Unqualified var) in
    let mono' = mono_of_poly_no_inst current in
    let%bind () = unify mono mono' in
    add_var var (Mono mono)
  in
  let%bind vars_list =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
         let%bind inner, mono = type_expr expr in
         let%map binding, mono, vars =
           type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
         in
         binding, (inner, mono), vars))
  in
  let typed_bindings, exprs, vars_list = List.unzip3 vars_list in
  let%bind () = incr_abstraction_level in
  let%bind () =
    List.map bindings ~f:(fun (inner, v) ->
      match v with
      | false ->
        State.Result.all_unit (List.map inner ~f:(gen_var ~add_var ~pop_var))
      | true -> return ())
    |> State.Result.all_unit
  in
  let%map () = decr_abstraction_level in
  let bindings = List.unzip bindings |> fst in
  typed_bindings, exprs, List.concat [ vars_list; bindings ]

and type_field expr field ~mut =
  let open State.Result.Let_syntax in
  let%bind type_proof, muta, poly = lookup_field field in
  let%bind () =
    match mut, muta with
    | true, `Immutable ->
      State.Result.error
        [%message "Field needs to be mutable" (field : Lowercase.t Qualified.t)]
    | _ -> return ()
  in
  let%bind named_poly = Named type_proof |> gen |> State.map ~f:Result.return in
  let%bind monos =
    inst_many [ named_poly; poly ] |> State.map ~f:Result.return
  in
  let type_proof, mono =
    match monos with
    | [ Named type_proof; mono ] -> type_proof, mono
    | _ -> assert false
  in
  let%bind inner, expr_mono = type_expr expr in
  let%bind () = unify expr_mono (Named type_proof) in
  let%map mono = apply_substs mono in
  (* result type, (expr for the LHS)*)
  mono, (inner, expr_mono)

and substitute (inner, mono) =
  let%map.State.Result mono = apply_substs mono in
  inner, mono

and type_expr expr =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node node -> type_node node >>= substitute
  | Ref expr ->
    let%bind inner, mono = type_expr expr in
    let%map mono = apply_substs mono in
    Typed_ast.Ref (inner, mono), Reference mono
  | Deref expr ->
    let%bind tyvar = gen_ty_var in
    let%bind inner, inner_mono = type_expr expr in
    let%bind () = unify inner_mono (Reference tyvar) in
    let%map mono = apply_substs tyvar in
    Typed_ast.Deref (inner, inner_mono), mono
  | Field_access (expr, field) ->
    let%bind mono, lhs_expr = type_field expr field ~mut:false in
    (Typed_ast.Field_access (lhs_expr, field), mono) |> substitute
  | Field_set (expr1, field, expr2) ->
    let%bind field_mono, lhs_expr = type_field expr1 field ~mut:true in
    let%bind ((_, rhs_mono) as rhs_expr) = type_expr expr2 in
    let%bind () = unify field_mono rhs_mono in
    (Typed_ast.Field_set (lhs_expr, field, rhs_expr), Named unit_type)
    |> substitute
  | If (pred, then_, else_) ->
    let%bind ((_, pred_mono) as pred_expr) = type_expr pred in
    let%bind ((_, then_mono) as then_expr) = type_expr then_ in
    let%bind ((_, else_mono) as else_expr) = type_expr else_ in
    let%bind () = unify pred_mono (Named bool_type) in
    let%bind () = unify then_mono else_mono in
    let%map then_mono = apply_substs then_mono in
    Typed_ast.If (pred_expr, then_expr, else_expr), then_mono
  | App (func, arg) ->
    let%bind ((_, func_mono) as func_expr) = type_expr func in
    let%bind ((_, arg_mono) as arg_expr) = type_expr arg in
    let%bind res_mono = gen_ty_var in
    let%bind state = State.Result.get in
    let non_closed () =
      let%bind () = unify func_mono (Function (arg_mono, res_mono)) in
      apply_substs res_mono
    in
    let closed () =
      match func_mono with
      | Closure (a, b, _) ->
        let%bind () = unify a arg_mono in
        let%bind () = unify b res_mono in
        apply_substs res_mono
      | _ -> State.Result.error [%sexp 1]
    in
    let%bind res_mono =
      match%bind.State non_closed () with
      | Ok res_mono -> return res_mono
      | Error _ as err ->
        let%bind () = State.Result.put state in
        (match%map.State closed () with
         | Ok _ as x -> x
         | Error _ -> err)
    in
    (Typed_ast.App (func_expr, arg_expr), res_mono) |> substitute
  | Typed (expr, ty) ->
    let%bind expr_inner, mono = type_expr expr in
    let%map mono =
      match ty.type_expr with
      | None -> apply_substs mono
      | Some ty ->
        let%bind ty_mono = type_of_type_expr ty in
        let%bind () = unify mono ty_mono in
        apply_substs mono
    in
    expr_inner, mono
  | Let_in (Ast.Nonrec (binding, expr1), expr2) ->
    let%bind binding, expr, vars =
      add_nonrec_bindings
        ~binding
        ~expr:expr1
        ~add_var_mono:(add_local_var_mono ~is_rec:false)
    in
    let%bind ((_, res_mono) as res_expr) = type_expr expr2 in
    let%bind () = State.Result.all_unit (List.map vars ~f:pop_local_var) in
    let%map res_mono = apply_substs res_mono in
    Typed_ast.(Let_in (Nonrec (binding, expr), res_expr)), res_mono
  | Let_in (Ast.Rec l, expr2) ->
    let%bind bindings, exprs, vars =
      add_rec_bindings
        ~add_var:(add_local_var ~is_rec:true)
        ~pop_var:pop_local_var
        l
    in
    let let_each_list = List.zip_exn bindings exprs in
    let%bind ((_, res_mono) as res_expr) = type_expr expr2 in
    let%bind () =
      State.Result.all_unit
        (List.map vars ~f:(fun vars ->
           State.Result.all_unit (List.map (List.rev vars) ~f:pop_local_var)))
    in
    let%map res_mono = apply_substs res_mono in
    Typed_ast.(Let_in (Rec let_each_list, res_expr)), res_mono
  | Match (expr1, cases) ->
    let%bind ((_, mono1) as expr1) = type_expr expr1 in
    let%bind cases =
      State.Result.all
        (List.map cases ~f:(fun (binding, expr2) ->
           let_each_of_binding_typed
             ~binding
             ~mono1
             ~expr2
             ~generalize:false
             ~value_restriction:false
             ~add_var_mono:(add_local_var_mono ~is_rec:false)
             ~pop_var:pop_local_var))
    in
    let%map mono =
      match cases with
      | [] -> State.Result.error [%message "Empty match"]
      | (_, (_, mono)) :: _ as l ->
        let%bind () =
          State.Result.all_unit
            (List.map l ~f:(fun (_, (_, mono')) -> unify mono mono'))
        in
        apply_substs mono
    in
    Typed_ast.(Match (expr1, cases)), mono
  | Lambda (binding, body) ->
    let%bind var = gen_ty_var in
    let%bind () = incr_abstraction_level in
    let%bind binding, (res_inner, res_mono) =
      let_each_of_binding_typed
        ~binding
        ~mono1:var
        ~expr2:body
        ~generalize:false
        ~value_restriction:false
        ~add_var_mono:(add_local_var_mono ~is_rec:false)
        ~pop_var:pop_local_var
    in
    let%bind var = apply_substs var in
    let%bind () = decr_abstraction_level in
    let%bind closed_vars = already_bound body in
    let%bind closed_vars =
      State.Result.all
      @@ List.map closed_vars ~f:(fun binding_id ->
        let%map { poly; _ } = lookup_binding_id binding_id in
        let mono = get_mono_from_poly_without_gen poly in
        binding_id, mono)
    in
    let%map res_mono = apply_substs res_mono in
    (match List.is_empty closed_vars with
     | true ->
       ( Typed_ast.Lambda (binding, (res_inner, res_mono))
       , Function (var, res_mono) )
     | false ->
       ( Typed_ast.Lambda (binding, (res_inner, res_mono))
       , Closure (var, res_mono, closed_vars) ))
;;

let type_let_def (let_def : Ast.let_def) =
  let open State.Result.Let_syntax in
  let%bind res =
    match let_def with
    | Ast.Rec l ->
      let%bind bindings, exprs, _ =
        add_rec_bindings l ~add_var:add_module_var ~pop_var:pop_module_var
      in
      let let_each_list = List.zip_exn bindings exprs in
      (* let%map () = *)
      (*   State.Result.all_unit *)
      (*     (List.map bindings ~f:(fun binding -> *)
      (*        State.Result.all_unit (List.map binding ~f:pop_var))) *)
      return @@ Typed_ast.Rec let_each_list
    | Ast.Nonrec (binding, expr) ->
      let%bind binding, expr, _ =
        add_nonrec_bindings ~binding ~expr ~add_var_mono:add_module_var_mono
      in
      (* let%map () = State.Result.all_unit (List.map binding ~f:pop_var) in *)
      return @@ Typed_ast.Nonrec (binding, expr)
  in
  let%bind state = State.Result.get in
  let%map () = State.Result.put { state with mono_ufds = Mono_ufds.empty } in
  res
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

let rec process_module_named (name : Uppercase.t Qualified.t) =
  let open State.Result.Let_syntax in
  let qualifications = Qualified.full_qualifications name in
  let%bind module_bindings = find_module_binding qualifications in
  let module_bindings =
    { module_bindings with data = Typed_ast.There module_bindings }
  in
  set_current_module_binding module_bindings

and process_struct (toplevels : Ast.toplevel list) =
  let open State.Result.Let_syntax in
  let%bind toplevels =
    State.Result.all @@ List.map ~f:type_toplevel toplevels
  in
  let%bind state = State.Result.get in
  let current_module_binding =
    { state.current_module_binding with data = Typed_ast.Here toplevels }
  in
  State.Result.put { state with current_module_binding }

and process_functor_app (f : Uppercase.t Qualified.t) (a : Ast.module_def list) =
  let _ = f, a in
  failwith "TODO"

and type_sig (toplevel_types : Ast.module_sig) =
  State.Result.all @@ List.map ~f:type_toplevel_type toplevel_types

and process_module_def (d : Ast.module_def) =
  match d with
  | Ast.Struct s -> process_struct s
  | Ast.Named f -> process_module_named f
  | Ast.Functor_app (f, a) -> process_functor_app f a
  | Ast.Module_typed (s, si) ->
    let _ = s, si in
    failwith "TODO"
(* let open State.Result.Let_syntax in *)
(* let%bind signature = type_sig si in *)
(* let%bind () = process_module_def s in *)
(* let%bind name, definition = pop_module in *)
(* let%bind module_ = unify_module_bindings ~signature ~definition in *)
(* change_to_module name module_ *)

and type_module_description _ = failwith "TODO"

and type_module
  ~(module_description : Ast.module_sig option Ast.module_description)
  ~(module_def : Ast.module_def)
  =
  let open State.Result.Let_syntax in
  let%bind () = change_to_new_module module_description.module_name in
  match module_description with
  | { module_name; functor_args = []; module_sig } ->
    let%bind sig_module_bindings =
      match module_sig with
      | Some module_sig ->
        let%bind _ = type_sig module_sig in
        let%bind name, module_ = pop_module in
        let%map () = change_to_new_module name in
        Some module_
      | None -> return None
    in
    let%bind () = process_module_def module_def in
    let%bind current_name, def_module_bindings = pop_module in
    let%bind module_bindings =
      match sig_module_bindings with
      | Some sig_module_bindings ->
        unify_module_bindings
          ~signature:sig_module_bindings
          ~definition:def_module_bindings
      | None -> return def_module_bindings
    in
    let%bind () = add_module ~name:current_name ~module_bindings in
    let open Typed_ast in
    let%map state = State.Result.get in
    let module_name = absolute_name ~state ~name:module_name in
    let module_description = { module_name; functor_args = [] } in
    Module_def (module_description, module_bindings)
  | _ -> failwith "TODO"

and type_toplevel_type (toplevel_type : Ast.toplevel_type) =
  match toplevel_type with
  | Ast.Sig_binding _ -> failwith "TODO"
  | Ast.Sig_module module_description ->
    type_module_description module_description
  | Ast.Sig_type_def _ -> failwith "TODO"

and type_toplevel (toplevel : Ast.toplevel) =
  let open State.Result.Let_syntax in
  match toplevel with
  | Ast.Type_def type_def -> type_type_def type_def
  | Ast.Let let_def ->
    let%map let_def = type_let_def let_def in
    Typed_ast.Let let_def
  | Ast.Module_def { module_description; module_def } ->
    type_module ~module_description ~module_def

and substitute_toplevel =
  let open State.Result.Let_syntax in
  function
  | Typed_ast.Type_def _ as x -> return x
  | Typed_ast.Module_def _ as x -> return x
  | Typed_ast.Let let_def ->
    let%map let_def = Typed_ast.map_let_def_monos_m ~f:apply_substs let_def in
    Typed_ast.Let let_def

and type_toplevel_list (l : Ast.t) =
  let%bind.State.Result l = State.Result.all (List.map l ~f:type_toplevel) in
  State.Result.all @@ List.map l ~f:substitute_toplevel
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

let mono_of_expr e = State.Result.map (type_expr e) ~f:snd

let process_file toplevel_list =
  let open State.Result.Let_syntax in
  let%bind toplevels = type_toplevel_list toplevel_list in
  let%map _, module_ = pop_module in
  { module_ with data = Typed_ast.Here toplevels }
;;
