open! Core
open! Shared
open! Frontend
open! Ty

module Mono_ufds = Ufds.Make (struct
  type t = mono [@@deriving sexp, equal, hash, compare]
end)

type module_history = {
  current_name : Uppercase.t;
  previous_modules : (Uppercase.t * module_bindings) list;
}
[@@deriving sexp, equal, compare, fields]

type state = {
  mono_ufds : Mono_ufds.t;
  current_module_binding : module_bindings;
  module_history : module_history;
  (* type_vars : (Lowercase.t * level) Lowercase.Map.t; *)
  (* current_level : level; *)
  symbol_n : int;
  type_map : type_constructor Int.Map.t;
}
[@@deriving sexp, equal, compare, fields]

let add_module ~name ~module_bindings =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let current_module_binding = state.current_module_binding in
  let current_module_binding =
    {
      current_module_binding with
      toplevel_modules =
        Uppercase.Map.set current_module_binding.toplevel_modules ~key:name
          ~data:module_bindings;
    }
  in
  State.Result.put { state with current_module_binding }

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

(* let get_level = *)
(*   let%map.State state = State.get in *)
(*   state.current_level *)

(* let incr_level = *)
(*   let%bind.State.Result state = State.Result.get in *)
(*   State.Result.put { state with current_level = state.current_level + 1 } *)

(* let decr_level = *)
(*   let%bind.State.Result state = State.Result.get in *)
(*   State.Result.put { state with current_level = state.current_level - 1 } *)

let add_type_constructor arg name user_type type_proof =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = (arg, user_type, type_proof) in
  let type_id = type_proof.type_id in
  let%bind type_map =
    match Int.Map.add state.type_map ~key:type_id ~data with
    | `Ok m -> return m
    | `Duplicate ->
        State.Result.error
          [%message
            "Duplicate type constructor" (name : Lowercase.t) (type_id : int)]
  in
  match
    Lowercase.Map.add state.current_module_binding.toplevel_type_constructors
      ~key:name ~data:type_id
  with
  | `Ok m ->
      State.Result.put
        {
          state with
          type_map;
          current_module_binding =
            { state.current_module_binding with toplevel_type_constructors = m };
        }
  | `Duplicate ->
      State.Result.error
        [%message "Duplicate type constructor" (name : Lowercase.t)]

let set_type_constructor arg name user_type type_proof =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = (arg, user_type, type_proof) in
  let type_id = type_proof.type_id in
  let type_map = Int.Map.set state.type_map ~key:type_id ~data in
  let toplevel_type_constructors =
    Lowercase.Map.set state.current_module_binding.toplevel_type_constructors
      ~key:name ~data:type_id
  in
  State.Result.put
    {
      state with
      type_map;
      current_module_binding =
        { state.current_module_binding with toplevel_type_constructors };
    }

let set_current_module_binding current_module_binding =
  State.Result.modify (fun state -> { state with current_module_binding })

let empty_state =
  {
    mono_ufds = Mono_ufds.empty;
    current_module_binding = empty_module_bindings;
    module_history = { current_name = ""; previous_modules = [] };
    symbol_n = 0;
    type_map = base_type_map;
  }

let gensym : string state_m =
  let open State.Let_syntax in
  let%bind state = State.get in
  let s = state.symbol_n in
  let%bind () = State.put { state with symbol_n = s + 1 } in
  let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
  let s = String.make 1 letter ^ Int.to_string (s / 26) in
  return s

let print_ufds_map : unit state_result_m =
  let open State.Result.Let_syntax in
  let%map state = State.Result.get in
  print_s [%message (state.mono_ufds : Mono_ufds.t)]

let add_type = add_type_constructor None

let add_var name poly =
  let open State.Let_syntax in
  let%bind state = State.get in
  let toplevel_vars =
    Lowercase.Map.add_multi state.current_module_binding.toplevel_vars ~key:name
      ~data:poly
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  State.Result.put { state with current_module_binding }

let pop_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let toplevel_vars =
    Lowercase.Map.remove_multi state.current_module_binding.toplevel_vars name
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  State.Result.put { state with current_module_binding }

let merge_variance_one variances ~name ~variance =
  Lowercase.Map.change variances name ~f:(function
    | None -> Some variance
    | Some x -> Some (Variance.merge x variance))

let merge_variance_maps (variances1 : Variance.t Lowercase.Map.t) variances2 =
  Lowercase.Map.merge variances1 variances2 ~f:(fun ~key:_ -> function
    | `Left x | `Right x -> Some x | `Both (x, y) -> Some (Variance.merge x y))

(* let rec type_constructor_variance_map = function *)
(*   | Single_arg (variance, name) -> Lowercase.Map.singleton name variance *)
(*   | Tuple_arg args -> *)
(*       List.fold args ~init:Lowercase.Map.empty ~f:(fun acc (variance, _) -> *)
(*           merge_variance_one acc variance) *)

let merge_variance_map_list =
  List.fold ~init:Lowercase.Map.empty ~f:merge_variance_maps

(* let rec calculate_variance mono = *)
(*   match mono with *)
(*   | Abstract (_, Some arg) -> type_constructor_variance_map arg *)
(*   | Abstract _ | TyVar _ -> Lowercase.Map.empty *)
(*   | Tuple l -> *)
(*       List.fold l ~init:Lowercase.Map.empty ~f:(fun acc mono -> *)
(*           merge_variance_maps acc (calculate_variance mono)) *)
(*   | Reference mono -> calculate_variance mono *)
(*   | Lambda (l, r) -> *)
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

let union mono1 mono2 : unit state_m =
  let%bind.State state = State.get in
  let mono_ufds = Mono_ufds.union state.mono_ufds mono1 mono2 in
  State.put { state with mono_ufds }

let ufds_find mono =
  let%map.State state = State.get in
  Mono_ufds.find state.mono_ufds mono

let rec search_modules :
    type a.
    module_bindings ->
    qualifications:Qualified.qualifications ->
    search_for:(module_bindings -> a option) ->
    a option =
  let find_in_opened_modules module_bindings ~qualifications ~search_for =
    List.find_map module_bindings.opened_modules
      ~f:(search_modules ~qualifications ~search_for)
  in
  fun module_bindings ~qualifications
      ~(search_for : module_bindings -> a option) ->
    match qualifications with
    | [] -> (
        match search_for module_bindings with
        | Some x -> Some x
        | None ->
            find_in_opened_modules module_bindings ~qualifications ~search_for)
    | name :: qualifications -> (
        let open Option.Let_syntax in
        let first =
          Uppercase.Map.find module_bindings.toplevel_modules name
          >>= search_modules ~qualifications ~search_for
        in
        match first with
        | Some _ -> first
        | None ->
            find_in_opened_modules module_bindings ~qualifications ~search_for)

let find_module_binding qualifications =
  let%bind.State state = State.get in
  match
    search_modules state.current_module_binding ~qualifications
      ~search_for:Option.some
  with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message
          "module not found" (qualifications : Qualified.qualifications)]

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> snd @@ List.unzip l
  | Single_arg (_, x) -> [ x ]

let ordering constructor_arg =
  Option.map constructor_arg ~f:constructor_arg_free_ty_vars
  |> Option.value ~default:[]

let tyvar_map ordering =
  List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc tyvar ->
      Lowercase.Map.add_exn acc ~key:tyvar ~data:(TyVar tyvar))

let lookup_type_map type_id =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match Int.Map.find state.type_map type_id with
  | Some x -> State.Result.return x
  | None -> State.Result.error [%message "type not found" (type_id : int)]

let lookup_type_constructor qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_type_constructors type_name)
  in
  match res with
  | Some type_id -> lookup_type_map type_id
  | None ->
      State.Result.error
        [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

let add_to_type_map ~type_id type_constructor =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match Int.Map.add state.type_map ~key:type_id ~data:type_constructor with
  | `Ok type_map -> State.Result.put { state with type_map }
  | `Duplicate ->
      State.Result.error [%message "duplicate type id" (type_id : int)]

let set_type_map ~type_id type_constructor =
  State.Result.modify (fun state ->
      let type_map =
        Int.Map.set state.type_map ~key:type_id ~data:type_constructor
      in
      { state with type_map })

let lookup_type ?(type_var = true) qualified_name =
  let open State.Result.Let_syntax in
  let qualifications, type_name = Qualified.split qualified_name in
  let type_var_fn = if type_var then Option.some else Fn.const None in
  let type_var_type =
    match qualifications with [] -> type_var_fn (TyVar type_name) | _ -> None
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

let get_type_proof mono =
  match mono with Named proof -> Some proof | _ -> None

let get_ordering (type_name : Lowercase.t Qualified.t) =
  let open State.Result.Let_syntax in
  let%map _, _, { ordering; _ } = lookup_type_constructor type_name in
  Option.value ordering ~default:[]

let rec show_type_proof { absolute_type_name; ordering; tyvar_map; _ } =
  let open State.Result.Let_syntax in
  let ordering = Option.value ordering ~default:[] in
  let%map type_var_map =
    List.map
      ~f:(fun k ->
        match Lowercase.Map.find tyvar_map k with
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

and show_mono mono =
  let open State.Result.Let_syntax in
  match mono with
  | Weak s | TyVar s -> return s
  | Named proof -> show_type_proof proof
  | Lambda (a, b) ->
      let%bind a = show_mono a in
      let%map b = show_mono b in
      a ^ " -> " ^ b
  | Tuple l ->
      let%map shown = List.map ~f:show_mono l |> State.Result.all in
      "(" ^ String.concat ~sep:", " shown ^ ")"
  | Reference m ->
      let%map m = show_mono m in
      "@" ^ m

let rec split_poly = function
  | Mono m -> (Lowercase.Set.empty, m)
  | Forall (a, b) ->
      let set, m = split_poly b in
      (Lowercase.Set.add set a, m)

let split_poly_to_list poly =
  let rec inner = function
    | Mono m -> ([], m)
    | Forall (a, b) ->
        let l, m = inner b in
        (a :: l, m)
  in
  inner poly |> Tuple2.map_fst ~f:List.rev

let show_mono_ufds (mono_ufds : Mono_ufds.t) =
  let open State.Result.Let_syntax in
  let%map alist =
    Map.to_alist mono_ufds
    |> List.map ~f:(fun (k, v) ->
           let%bind k = show_mono k in
           let%map v = show_mono v in
           (k, v))
    |> State.Result.all
  in
  [%message (alist : (string * string) list)]

let lookup_var qualified_name : _ state_result_m =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_vars type_name)
  in
  match res with
  | Some (x :: _) -> State.Result.return x
  | None | Some [] ->
      State.Result.error
        [%message "var not in scope" (qualified_name : Lowercase.t Qualified.t)]

let map_user_type_m user_type ~f =
  let open State.Result.Let_syntax in
  match user_type with
  | Abstract -> return user_type
  | Record l ->
      let%map l =
        State.Result.all
          (List.map l ~f:(fun (x, (y, mut)) ->
               let%map y = f y in
               (x, (y, mut))))
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
               (x, y)))
      in
      Enum l
  | User_mono mono ->
      let%map mono = f mono in
      User_mono mono

let map_user_type user_type ~f =
  let f x = State.Result.return (f x) in
  map_user_type_m user_type ~f

let rec map_ty_vars ~f (mono : mono) =
  match mono with
  | TyVar m -> Option.value (f m) ~default:mono
  | Weak _ -> mono
  | Lambda (a, b) -> Lambda (map_ty_vars ~f a, map_ty_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_ty_vars ~f))
  | Named type_proof -> Named (map_type_proof ~f type_proof)
  | Reference x -> Reference (map_ty_vars ~f x)

and map_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  {
    type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_ty_vars ~f);
  }

let map_user_type_ty_vars ~f = map_user_type ~f:(map_ty_vars ~f)

let rec map_ty_vars_m ~f (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | TyVar m -> f m
  | Weak _ -> return mono
  | Lambda (a, b) ->
      let%bind a = map_ty_vars_m ~f a in
      let%map b = map_ty_vars_m ~f b in
      Lambda (a, b)
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
    Lowercase.Map.fold tyvar_map ~init:(return Lowercase.Map.empty)
      ~f:(fun ~key ~data acc ->
        let%bind acc = acc in
        let%map data = map_ty_vars_m ~f data in
        Lowercase.Map.set acc ~key ~data)
  in
  { type_proof with tyvar_map }

let map_user_type_ty_vars_m ~f = map_user_type_m ~f:(map_ty_vars_m ~f)

let rec map_weak_vars ~f (mono : mono) =
  match mono with
  | Weak m -> Option.value (f m) ~default:mono
  | TyVar _ -> mono
  | Lambda (a, b) -> Lambda (map_weak_vars ~f a, map_weak_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_weak_vars ~f))
  | Reference x -> Reference (map_weak_vars ~f x)
  | Named type_proof -> Named (map_weak_type_proof ~f type_proof)

and map_weak_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  {
    type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_weak_vars ~f);
  }

let map_user_type_weak_vars ~f = map_user_type ~f:(map_weak_vars ~f)
let make_weak mono = map_ty_vars mono ~f:(fun x -> Some (Weak x))

let iter_ty_vars ~f mono =
  ignore
    (map_ty_vars mono ~f:(fun x ->
         f x;
         None))

let iter_weak_vars ~f mono =
  ignore
    (map_weak_vars mono ~f:(fun x ->
         f x;
         None))

let free_ty_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_ty_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x);
  !set

let free_ty_vars_list monos =
  let set = ref Lowercase.Set.empty in
  List.iter monos ~f:(fun mono ->
      iter_ty_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x));
  !set

let free_weak_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_weak_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x);
  !set

let replace_ty_vars ~replacement_map =
  map_ty_vars ~f:(Lowercase.Map.find replacement_map)

let replace_ty_vars_type_proof ~replacement_map =
  map_type_proof ~f:(Lowercase.Map.find replacement_map)

let no_free_vars poly =
  let set, mono = split_poly poly in
  let set' = free_ty_vars mono in
  Lowercase.Set.equal set set'

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
      Lambda (first, second)
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (first, second) ->
      let%bind constructor_arg, _, type_proof =
        lookup_type_constructor second
      in
      let%bind arg = type_of_type_expr first in
      let vars =
        match constructor_arg with
        | None -> []
        | Some (Single_arg (_, x)) -> [ x ]
        | Some (Tuple_arg l) -> List.unzip l |> snd
      in
      let arg_list = match arg with Tuple l -> l | _ -> [ arg ] in
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

let gen (mono : mono) : poly state_m =
  free_ty_vars mono
  |> Lowercase.Set.fold ~init:(Mono mono) ~f:(fun acc var -> Forall (var, acc))
  |> State.return

let add_constructor name arg result =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match
    Uppercase.Map.add state.current_module_binding.toplevel_constructors
      ~key:name ~data:(arg, result)
  with
  | `Ok toplevel_constructors ->
      State.Result.put
        {
          state with
          current_module_binding =
            { state.current_module_binding with toplevel_constructors };
        }
  | `Duplicate ->
      State.Result.error
        [%message "duplicate constructor" ~constructor:(name : Uppercase.t)]

let add_field field poly =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match
    Lowercase.Map.add state.current_module_binding.toplevel_fields ~key:field
      ~data:poly
  with
  | `Ok toplevel_fields ->
      State.Result.put
        {
          state with
          current_module_binding =
            { state.current_module_binding with toplevel_fields };
        }
  | `Duplicate ->
      State.Result.error
        [%message "duplicate field" ~field:(field : Lowercase.t)]

let add_record field_map type_proof : _ state_result_m =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let%bind field_set =
    Lowercase.Map.fold field_map ~init:(return Lowercase.Set.empty)
      ~f:(fun ~key ~data:(poly, mut) acc ->
        let%bind acc = acc in
        let%map () = add_field key (type_proof, mut, poly) in
        Lowercase.Set.add acc key)
  in
  let field_map = Lowercase.Map.map field_map ~f:fst in
  match
    Lowercase.Set.Map.add state.current_module_binding.toplevel_records
      ~key:field_set ~data:(field_map, type_proof)
  with
  | `Ok toplevel_records ->
      State.Result.put
        {
          state with
          current_module_binding =
            { state.current_module_binding with toplevel_records };
        }
  | `Duplicate ->
      State.Result.error
        [%message "duplicate record" (field_set : Lowercase.Set.t)]

let lookup_record qualified_map =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, map = Qualified.split qualified_map in
  let fields =
    Lowercase.Map.fold map ~init:Lowercase.Set.empty ~f:(fun ~key ~data:_ acc ->
        Lowercase.Set.add acc key)
  in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Set.Map.find module_bindings.toplevel_records fields)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "record not in scope" (fields : Lowercase.Set.t)]

let lookup_constructor qualified_constructor =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_constructor in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Uppercase.Map.find module_bindings.toplevel_constructors name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "constructor not in scope" (name : Uppercase.t)]

let lookup_field qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_name in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_fields name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error [%message "field not in scope" (name : Lowercase.t)]

let type_proof_of_monos ~type_name ~absolute_type_name ~ordering monos type_id =
  let free_var_set =
    List.fold monos ~init:Lowercase.Set.empty ~f:(fun acc mono ->
        Lowercase.Set.union acc (free_ty_vars mono))
  in
  let tyvar_map =
    Lowercase.Set.fold free_var_set ~init:Lowercase.Map.empty ~f:(fun acc x ->
        Lowercase.Map.add_exn acc ~key:x ~data:(TyVar x))
  in
  { type_name; absolute_type_name; tyvar_map; ordering; type_id }

let absolute_type_name ~state ~type_name =
  let rec inner curr l =
    match l with
    | [] -> curr
    | (u, _) :: rest -> inner (Qualified.Qualified (u, curr)) rest
  in
  let { current_name; previous_modules } = state.module_history in
  let init =
    match current_name with
    | "" -> Qualified.Unqualified type_name
    | _ -> Qualified.Qualified (current_name, Qualified.Unqualified type_name)
  in
  inner init previous_modules

let type_of_type_def_lit ~(type_name : string) ~type_id ~ordering
    (type_def_lit : Ast.Type_def_lit.t) =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let absolute_type_name = absolute_type_name ~state ~type_name in
  match type_def_lit with
  | Ast.Type_def_lit.Type_expr type_expr ->
      let%map mono = type_of_type_expr type_expr in
      let type_proof =
        {
          type_name;
          absolute_type_name;
          tyvar_map =
            free_ty_vars mono
            |> Lowercase.Set.fold ~init:Lowercase.Map.empty ~f:(fun acc x ->
                   Lowercase.Map.add_exn ~key:x ~data:(TyVar x) acc);
          ordering;
          type_id;
        }
      in
      (type_proof, User_mono mono)
  | Ast.Type_def_lit.Record l ->
      let%bind record_type =
        List.map l ~f:(fun (name, (type_expr, mutability)) ->
            let%map mono = type_of_type_expr type_expr in
            (name, (mono, mutability)))
        |> State.Result.all
      in
      let type_proof =
        type_proof_of_monos ~type_name ~absolute_type_name ~ordering
          (List.map record_type ~f:(Fn.compose fst snd))
          type_id
      in
      let user_type = Record record_type in
      let%bind polys =
        State.Result.all
          (List.map record_type ~f:(fun (field, (mono, mut)) ->
               let%map.State poly = gen mono in
               Ok (field, poly, mut)))
      in
      let field_map =
        List.fold polys ~init:Lowercase.Map.empty
          ~f:(fun acc (field, poly, mut) ->
            Lowercase.Map.add_exn acc ~key:field ~data:(poly, mut))
      in
      let%map () = add_record field_map type_proof in
      (type_proof, user_type)
  | Ast.Type_def_lit.Enum l ->
      let%bind enum_type =
        List.map l ~f:(fun (name, type_expr) ->
            let%map mono =
              match type_expr with
              | Some type_expr -> type_of_type_expr type_expr >>| Option.some
              | None -> return None
            in
            (name, mono))
        |> State.Result.all
      in
      let monos = List.filter_map enum_type ~f:(fun (_, mono) -> mono) in
      let type_proof =
        type_proof_of_monos ~type_name ~absolute_type_name ~ordering monos
          type_id
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
      (type_proof, user_type)

let set_ordering (mono : mono) ~ordering =
  match mono with
  | Named p -> Named { p with ordering = Some ordering }
  | _ -> mono

let process_type_def
    ({ type_name; type_def; ast_tags = _ } :
      Ast.Type_def_lit.t Ast.type_description) =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match type_name with
  | Ast.Type_binding.Mono type_name -> (
      let absolute_type_name = absolute_type_name ~state ~type_name in
      let type_id = type_id_of_absolute_name absolute_type_name in
      let%bind type_proof, user_type =
        type_of_type_def_lit ~type_name ~type_id ~ordering:None type_def
      in
      match Lowercase.Map.length type_proof.tyvar_map with
      | 0 -> add_type type_name user_type type_proof
      | _ ->
          State.Result.error
            [%message
              "type definition has free type variables"
                (user_type : user_type)
                ~vars:
                  (Lowercase.Map.to_alist type_proof.tyvar_map
                   |> List.map ~f:fst
                    : Lowercase.t list)
                (type_name : Lowercase.t)])
  | Ast.Type_binding.Poly (arg, type_name) -> (
      let absolute_type_name = absolute_type_name ~state ~type_name in
      let type_id = type_id_of_absolute_name absolute_type_name in
      let constructor_arg =
        match arg with
        | Ast.Type_binding.Single (v, l) -> Some (Single_arg (v, l))
        | Ast.Type_binding.Tuple l -> Some (Tuple_arg l)
      in
      let ordering = ordering constructor_arg in
      let lhs_ty_vars =
        List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc key ->
            Lowercase.Map.add_exn acc ~key ~data:(TyVar key))
      in
      let type_proof =
        {
          type_name;
          absolute_type_name;
          ordering = Some ordering;
          type_id;
          tyvar_map = lhs_ty_vars;
        }
      in
      let%bind () =
        add_type_constructor constructor_arg type_name Abstract type_proof
      in
      let%bind type_proof', user_type =
        type_of_type_def_lit ~type_name ~type_id ~ordering:(Some ordering)
          type_def
      in
      let rhs_ty_vars =
        Lowercase.Map.key_set type_proof'.tyvar_map |> Obj.magic
      in
      let lhs_ty_vars = Lowercase.Map.key_set lhs_ty_vars |> Obj.magic in
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
                (rhs_ty_vars : Lowercase.Set.t)])

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
          Lowercase.Map.set replacement_map ~key:a ~data:(TyVar rep)
        in
        Forall (rep, inner ~replacement_map poly)
  in
  inner ~replacement_map:Lowercase.Map.empty poly

let inst (poly : poly) : mono state_m =
  let open State.Let_syntax in
  let rec inner ~replacement_map poly =
    match poly with
    | Mono x -> return (replace_ty_vars ~replacement_map x)
    | Forall (a, poly) ->
        let%bind sym = gensym in
        let replacement_map =
          Lowercase.Map.set replacement_map ~key:a ~data:(TyVar sym)
        in
        inner ~replacement_map poly
  in
  inner ~replacement_map:Lowercase.Map.empty poly

let inst_result x = State.map (inst x) ~f:Result.return

let inst_type_proof type_proof =
  let open State.Result.Let_syntax in
  let%map replacement_map =
    Lowercase.Map.fold type_proof.tyvar_map ~init:(return Lowercase.Map.empty)
      ~f:(fun ~key ~data:_ acc ->
        let%bind acc = acc in
        let%map sym =
          match Lowercase.Map.find acc key with
          | Some x -> return x
          | None ->
              let%map res = State.map gensym ~f:Result.return in
              TyVar res
        in
        Lowercase.Map.set acc ~key ~data:sym)
  in
  replace_ty_vars_type_proof ~replacement_map type_proof

let unification_error mono1 mono2 =
  let%bind.State.Result a = show_mono mono1 in
  let%bind.State.Result b = show_mono mono2 in
  State.Result.error
    [%message "failed to unify types" ~_:(a : string) ~_:(b : string)]

let split_poly_list l =
  let set, monos =
    List.fold l ~init:(Lowercase.Set.empty, []) ~f:(fun (set, monos) poly ->
        let new_vars, mono = split_poly poly in
        (Lowercase.Set.union set new_vars, mono :: monos))
  in
  (set, List.rev monos)

let inst_many poly_list =
  let open State.Let_syntax in
  let quantifiers, mono_list = split_poly_list poly_list in
  let%map replacement_map =
    Lowercase.Set.to_list quantifiers
    |> List.map ~f:(fun var ->
           let%map sym = gensym in
           (var, TyVar sym))
    |> State.all >>| Lowercase.Map.of_alist_exn
  in
  List.map mono_list ~f:(replace_ty_vars ~replacement_map)

let inst_constructor constructor =
  let open State.Result.Let_syntax in
  let%bind arg, type_proof = lookup_constructor constructor in
  match arg with
  | None ->
      let%map type_proof = inst_type_proof type_proof in
      (None, Named type_proof)
  | Some poly_arg ->
      let%map mono_arg, mono_res =
        match%bind.State inst_many [ poly_arg; Mono (Named type_proof) ] with
        | [ mono_arg; mono_res ] -> return (mono_arg, mono_res)
        | _ ->
            State.Result.error
              [%message "inst_many returned wrong number of monos"]
      in
      (Some mono_arg, mono_res)

let type_of_constructor constructor =
  let open State.Result.Let_syntax in
  match%map inst_constructor constructor with
  | None, mono -> mono
  | Some mono_arg, mono_res -> Lambda (mono_arg, mono_res)

let occurs_check a mono =
  let open State.Result.Let_syntax in
  let free_vars = free_ty_vars mono in
  match Lowercase.Set.mem free_vars a with
  | true ->
      State.Result.error
        [%message "occurs check failed" (a : Lowercase.t) (mono : mono)]
  | false -> return ()

let rec reach_end_type_proof type_proof =
  let open State.Result.Let_syntax in
  match%bind.State lookup_type_map type_proof.type_id with
  | Ok (_, _, { type_name; type_id; _ })
    when not @@ phys_equal type_id type_proof.type_id ->
      reach_end_type_proof { type_proof with type_name; type_id }
  | _ -> return type_proof

let reach_end (mono : mono) =
  let%bind.State mono = find mono in
  match mono with
  | Named type_proof ->
      let%map.State.Result x = reach_end_type_proof type_proof in
      Named x
  | _ -> State.Result.return mono

let rec unify mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind mono1 = reach_end mono1 in
  let%bind mono2 = reach_end mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match (mono1, mono2) with
  | Named p1, Named p2 -> unify_type_proof p1 p2
  | TyVar x, TyVar y when String.equal x y -> State.Result.return ()
  | TyVar x, _ ->
      let%bind () = occurs_check x mono2 in
      State.map (union mono2 mono1) ~f:Result.return
  | _, TyVar x ->
      let%bind () = occurs_check x mono1 in
      State.map (union mono1 mono2) ~f:Result.return
  | Weak x, Weak y when String.equal x y -> State.Result.return ()
  | Weak x, _ ->
      let%bind () = occurs_check x mono2 in
      State.map (union mono2 mono1) ~f:Result.return
  | _, Weak x ->
      let%bind () = occurs_check x mono1 in
      State.map (union mono1 mono2) ~f:Result.return
  | Reference x, Reference y -> unify x y
  | Lambda (x1, x2), Lambda (y1, y2) ->
      let%bind () = unify x1 y1 in
      unify x2 y2
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
  let monos1 = Lowercase.Map.data rep1 in
  let%bind monos1 = State.Result.all (List.map ~f:reach_end monos1) in
  let monos2 = Lowercase.Map.data rep2 in
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

let rec unify_less_general mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind mono1 = reach_end mono1 in
  let%bind mono2 = reach_end mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match (mono1, mono2) with
  | Named p1, Named p2 -> unify_less_general_type_proof ~unification_error p1 p2
  | TyVar x, TyVar y when String.equal x y -> State.Result.return ()
  | TyVar _, _ -> unification_error ()
  | _, TyVar x ->
      let%bind () = occurs_check x mono1 in
      State.map (union mono1 mono2) ~f:Result.return
  | Weak x, Weak y when String.equal x y -> State.Result.return ()
  | Weak _, _ -> unification_error ()
  | _, Weak x ->
      let%bind () = occurs_check x mono1 in
      State.map (union mono1 mono2) ~f:Result.return
  | Reference x, Reference y -> unify_less_general x y
  | Lambda (x1, x2), Lambda (y1, y2) ->
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
  let monos1 = Lowercase.Map.data rep1 in
  let%bind monos1 = State.Result.all (List.map ~f:reach_end monos1) in
  let monos2 = Lowercase.Map.data rep2 in
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

let open_module (qualifications : Qualified.qualifications) =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let%bind module_bindings = find_module_binding qualifications in
  let current_module_binding =
    {
      current_module_binding with
      opened_modules = module_bindings :: current_module_binding.opened_modules;
    }
  in
  State.Result.put { state with current_module_binding }

let pop_opened_module =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let opened_modules =
    match current_module_binding.opened_modules with [] -> [] | _ :: xs -> xs
  in
  let current_module_binding = { current_module_binding with opened_modules } in
  State.Result.put { state with current_module_binding }

let change_to_module name module_bindings =
  let open State.Result.Let_syntax in
  let%bind ({ current_module_binding = old_module_binding; _ } as state) =
    State.Result.get
  in
  let { current_name; previous_modules } = state.module_history in
  let module_history =
    {
      current_name = name;
      previous_modules = (current_name, old_module_binding) :: previous_modules;
    }
  in
  let current_module_binding =
    {
      module_bindings with
      opened_modules = old_module_binding :: old_module_binding.opened_modules;
    }
  in
  State.Result.put { state with current_module_binding; module_history }

let change_to_new_module name = change_to_module name empty_module_bindings

let pop_module =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let old_module_binding = state.current_module_binding in
  let { current_name; previous_modules } = state.module_history in
  let current_module_binding, module_history =
    match previous_modules with
    | [] -> (empty_module_bindings, { current_name; previous_modules = [] })
    | (name, current_module_binding) :: xs ->
        (current_module_binding, { current_name = name; previous_modules = xs })
  in
  let%map () =
    State.Result.put { state with current_module_binding; module_history }
  in
  (current_name, old_module_binding)

let pop_module_and_add ~module_bindings =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let { current_name; previous_modules } = state.module_history in
  let%bind current_module_binding, module_history =
    match previous_modules with
    | [] -> State.Result.error [%message "No previous modules"]
    | (name, current_module_binding) :: xs ->
        return
          ( current_module_binding,
            { current_name = name; previous_modules = xs } )
  in
  let%bind () =
    State.Result.put { state with current_module_binding; module_history }
  in
  add_module ~name:current_name ~module_bindings

let pop_module_and_add_current =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  pop_module_and_add ~module_bindings:state.current_module_binding

let make_free_vars_weak mono =
  let free_vars = free_ty_vars mono in
  let replacement_map =
    Lowercase.Set.to_map free_vars ~f:(fun x -> Weak x) |> Obj.magic
  in
  replace_ty_vars ~replacement_map mono

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
      Lowercase.Map.exists ~f:value_restriction l
  | Ast.Wrapped qualified ->
      let _, l = Qualified.split qualified in
      value_restriction l

let gen_ty_var : _ state_result_m =
  let%map.State sym = gensym in
  Ok (TyVar sym)

let mono_of_literal literal =
  match literal with
  | Ast.Literal.Int _ -> State.Result.return (Named int_type)
  | Ast.Literal.Float _ -> State.Result.return (Named float_type)
  | Ast.Literal.Bool _ -> State.Result.return (Named bool_type)
  | Ast.Literal.Unit -> State.Result.return (Named unit_type)
  | Ast.Literal.String _ -> State.Result.return (Named string_type)
  | Ast.Literal.Char _ -> State.Result.return (Named char_type)

let poly_of_mono mono ~generalize ~value_restriction =
  match (generalize, value_restriction) with
  | false, _ -> State.Result.return @@ Mono mono
  | true, false -> State.map (gen mono) ~f:Result.return
  | true, true -> State.Result.return @@ Mono (make_weak mono)

let apply_substs mono =
  let%map.State state = State.get in
  let mono =
    map_ty_vars mono ~f:(fun mono ->
        let mono, _ = Mono_ufds.find state.mono_ufds (TyVar mono) in
        Some mono)
  in
  Ok
    (map_weak_vars mono ~f:(fun mono ->
         let mono, _ = Mono_ufds.find state.mono_ufds (Weak mono) in
         Some mono))

let lookup_in_type_proof mono ~look_for =
  let open State.Result.Let_syntax in
  match get_type_proof mono with
  | None -> State.Result.error [%message "can't find type proof" (mono : mono)]
  | Some { tyvar_map; _ } -> (
      match Lowercase.Map.find tyvar_map look_for with
      | Some x -> return x
      | None ->
          State.Result.error
            [%message
              "failed to find in type proof"
                (look_for : Lowercase.t)
                (mono : mono)])

let rec mono_of_poly_no_inst poly =
  match poly with Mono mono -> mono | Forall (_, r) -> mono_of_poly_no_inst r

exception Field_left_only of string
exception Field_right_only of string

let rec gen_binding_ty_vars ~initial_vars ~(binding : Ast.Binding.t) :
    (mono * Lowercase.t list) state_result_m =
  let open State.Result.Let_syntax in
  match binding with
  | Ast.Binding.Literal l ->
      let%map mono = mono_of_literal l in
      (mono, initial_vars)
  | Ast.Binding.Name var ->
      let%bind ty_var = gen_ty_var in
      let poly = Mono ty_var in
      let%map () = add_var var poly in
      (ty_var, var :: initial_vars)
  | Ast.Binding.Constructor (constructor, rest) -> (
      let%bind mono_arg, mono_res = inst_constructor constructor in
      match (rest, mono_arg) with
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
          let%bind mono, vars = gen_binding_ty_vars ~initial_vars ~binding in
          let%map () = unify mono_arg mono in
          (mono_res, vars))
  | Ast.Binding.Typed (binding, value_tag) -> (
      let type_expr = value_tag.Ast.Value_tag.type_expr in
      match type_expr with
      | None -> gen_binding_ty_vars ~initial_vars ~binding
      | Some type_expr ->
          let%bind tagged_mono = type_of_type_expr type_expr in
          let%bind mono, vars = gen_binding_ty_vars ~initial_vars ~binding in
          let%map () = unify tagged_mono mono in
          (mono, vars))
  | Ast.Binding.Pointer binding ->
      let%map mono, vars = gen_binding_ty_vars ~initial_vars ~binding in
      (Reference mono, vars)
  | Ast.Binding.Renamed (binding, var) ->
      let%bind mono, vars = gen_binding_ty_vars ~initial_vars ~binding in
      let%map () = add_var var (Mono mono) in
      (mono, var :: vars)
  | Ast.Binding.Tuple qualified ->
      let qualifications, tuple = Qualified.split qualified in
      let%bind () = open_module qualifications in
      let%bind processed_list =
        State.Result.all
          (List.map tuple ~f:(fun binding ->
               gen_binding_ty_vars ~initial_vars:[] ~binding))
      in
      let monos, vars_list = List.unzip processed_list in
      let vars = List.concat (List.rev vars_list) in
      let%map () = pop_opened_module in
      (Tuple monos, List.concat [ vars; initial_vars ])
  | Ast.Binding.Record qualified_map ->
      let qualifications, record = Qualified.split qualified_map in
      let%bind () = open_module qualifications in
      let%bind field_map, type_proof = lookup_record qualified_map in
      let%bind type_proof = inst_type_proof type_proof in
      let mono_searched = Named type_proof in
      let%bind field_map =
        try
          return
          @@ Lowercase.Map.merge record field_map ~f:(fun ~key -> function
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
        Lowercase.Map.fold field_map ~init:(State.Result.return [])
          ~f:(fun ~key:_ ~data:(binding, poly) acc ->
            let%bind vars_list = acc in
            let mono = mono_of_poly_no_inst poly in
            let%bind mono =
              map_ty_vars_m mono ~f:(fun v ->
                  lookup_in_type_proof mono_searched ~look_for:v)
            in
            let%bind mono', vars =
              gen_binding_ty_vars ~initial_vars:[] ~binding
            in
            let%map () = unify mono mono' in
            vars :: vars_list)
      in
      let res_vars = List.concat (List.rev vars_list) in
      let%map () = pop_opened_module in
      (mono_searched, List.concat [ res_vars; initial_vars ])

let gen_var var =
  let open State.Result.Let_syntax in
  let%bind value = lookup_var (Qualified.Unqualified var) in
  let%bind () = pop_var var in
  let%bind mono = inst_result value in
  let%bind mono = apply_substs mono in
  let%bind poly = State.Result.t_of_state (gen mono) in
  add_var var poly

let rec mono_of_node node =
  let open State.Result.Let_syntax in
  match node with
  | Ast.Literal literal -> mono_of_literal literal
  | Ast.Var var_name -> lookup_var var_name >>= inst_result
  | Ast.Tuple qualified_tuple ->
      let qualifications, tuple = Qualified.split qualified_tuple in
      let%bind () = open_module qualifications in
      let%bind l = State.Result.all (List.map tuple ~f:mono_of_expr) in
      let%map () = pop_opened_module in
      Tuple l
  | Ast.Wrapped qualified_expr ->
      let qualifications, expr = Qualified.split qualified_expr in
      let%bind () = open_module qualifications in
      let%bind res = mono_of_expr expr in
      let%map () = pop_opened_module in
      res
  | Ast.Constructor constructor -> type_of_constructor constructor
  | Ast.Record qualified_record ->
      let qualifications, record = Qualified.split qualified_record in
      let%bind () = open_module qualifications in
      let%bind field_map, type_proof =
        lookup_record (Qualified.Unqualified record)
      in
      let%bind type_proof = inst_type_proof type_proof in
      let mono_res = Named type_proof in
      let field_list = Lowercase.Map.to_alist field_map in
      (* lookup the tyvar in the map thingo in mono_res *)
      let%bind field_mono_map =
        List.map field_list ~f:(fun (field, poly) ->
            let mono = mono_of_poly_no_inst poly in
            let%map mono =
              map_ty_vars_m mono ~f:(fun v ->
                  lookup_in_type_proof mono_res ~look_for:v)
            in
            (field, mono))
        |> State.Result.all >>| Lowercase.Map.of_alist_exn
      in
      let%bind () =
        Lowercase.Map.fold record ~init:(State.Result.return ())
          ~f:(fun ~key:field ~data:expr acc ->
            let%bind () = acc in
            let%bind mono = mono_of_expr expr in
            match Lowercase.Map.find field_mono_map field with
            | None ->
                State.Result.error
                  [%message "Unknown field" (field : Lowercase.t)]
            | Some field_mono -> unify field_mono mono)
      in
      apply_substs mono_res

and add_var_mono ~generalize ~value_restriction var mono =
  let open State.Result.Let_syntax in
  let%bind poly = poly_of_mono ~generalize ~value_restriction mono in
  add_var var poly

and process_binding ~act_on_var ~initial_vars ~(binding : Ast.Binding.t) ~mono :
    (mono * Lowercase.t list) state_result_m =
  let open State.Result.Let_syntax in
  match binding with
  | Ast.Binding.Literal l ->
      let%bind binding_mono = mono_of_literal l in
      let%map () = unify binding_mono mono in
      (mono, initial_vars)
  | Ast.Binding.Name var ->
      (* let%bind poly = poly_of_mono ~generalize ~value_restriction mono in *)
      (* let%map () = act_on_var var poly in *)
      let%map () = act_on_var var mono in
      (mono, var :: initial_vars)
  | Ast.Binding.Constructor (constructor, rest) -> (
      let%bind mono_arg, mono_res = inst_constructor constructor in
      match (rest, mono_arg) with
      | None, None -> return (mono_res, [])
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
          let%bind _, vars =
            process_binding ~act_on_var ~initial_vars ~binding ~mono:mono_arg
          in
          let%bind () = unify mono_res mono in
          return (mono_res, vars))
  | Ast.Binding.Typed (binding, value_tag) -> (
      let type_expr = value_tag.Ast.Value_tag.type_expr in
      match type_expr with
      | None -> process_binding ~act_on_var ~initial_vars ~binding ~mono
      | Some type_expr ->
          let%bind tagged_mono = type_of_type_expr type_expr in
          let%bind () = unify tagged_mono mono in
          let%bind mono_res, vars =
            process_binding ~act_on_var ~initial_vars ~binding ~mono
          in
          let%map () = unify mono_res tagged_mono in
          (mono, vars))
  | Ast.Binding.Renamed (binding, var) ->
      let%bind mono, vars =
        process_binding ~act_on_var ~initial_vars ~binding ~mono
      in
      let%map () = act_on_var var mono in
      (mono, var :: vars)
  | Ast.Binding.Pointer binding ->
      let%bind ty_var = gen_ty_var in
      let%bind () = unify (Reference ty_var) mono in
      let%map mono, vars =
        process_binding ~act_on_var ~initial_vars ~binding ~mono:ty_var
      in
      (mono, vars)
  | Ast.Binding.Tuple qualified ->
      let qualifications, tuple = Qualified.split qualified in
      let%bind () = open_module qualifications in
      let%bind arg_monos =
        match mono with
        | Tuple list ->
            if List.length list <> List.length tuple then
              State.Result.error
                [%message
                  "Tuple length mismatch"
                    (mono : mono)
                    (tuple : Ast.Binding.t list)]
            else State.Result.return list
        | _ -> State.Result.error [%message "Expected tuple" (mono : mono)]
      in
      let tuple_zipped = List.zip_exn tuple arg_monos in
      let%bind processed_list =
        State.Result.all
          (List.map tuple_zipped ~f:(fun (binding, mono) ->
               process_binding ~act_on_var ~initial_vars:[] ~binding ~mono))
      in
      let monos, vars_list = List.unzip processed_list in
      let vars = List.concat (List.rev vars_list) in
      let%map () = pop_opened_module in
      (Tuple monos, List.concat [ vars; initial_vars ])
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
          @@ Lowercase.Map.merge record field_map ~f:(fun ~key -> function
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
        Lowercase.Map.fold field_map ~init:(State.Result.return [])
          ~f:(fun ~key:_ ~data:(binding, poly) acc ->
            let%bind vars_list = acc in
            let mono = mono_of_poly_no_inst poly in
            let%bind mono =
              map_ty_vars_m mono ~f:(fun v ->
                  lookup_in_type_proof mono_searched ~look_for:v)
            in
            let%bind mono', vars =
              process_binding ~act_on_var ~initial_vars:[] ~binding ~mono
            in
            let%map () = unify mono' mono in
            vars :: vars_list)
      in
      let res_vars = List.concat (List.rev vars_list) in
      let%map () = pop_opened_module in
      (mono_searched, List.concat [ res_vars; initial_vars ])

and mono_of_binding_typed ~(binding : Ast.Binding.t) ~mono1 ~expr2 ~generalize
    ~value_restriction =
  let open State.Result.Let_syntax in
  let act_on_var = add_var_mono ~generalize ~value_restriction in
  let%bind mono, vars =
    process_binding ~act_on_var ~initial_vars:[] ~binding ~mono:mono1
  in
  let%bind () = unify mono mono1 in
  let%bind res = mono_of_expr expr2 in
  let%map () = State.Result.all_unit (List.map vars ~f:pop_var) in
  res

and mono_of_binding ~(binding : Ast.Binding.t) ~expr1 ~expr2 ~generalize =
  let open State.Result.Let_syntax in
  let value_restriction = value_restriction expr1 in
  let%bind mono1 = mono_of_expr expr1 in
  let%bind mono1 = apply_substs mono1 in
  mono_of_binding_typed ~binding ~mono1 ~expr2 ~generalize ~value_restriction

and add_nonrec_bindings ~binding ~expr =
  let open State.Result.Let_syntax in
  let value_restriction = value_restriction expr in
  let%bind mono = mono_of_expr expr in
  let%bind mono = apply_substs mono in
  let act_on_var = add_var_mono ~generalize:true ~value_restriction in
  let%bind mono', vars =
    process_binding ~act_on_var ~initial_vars:[] ~binding ~mono
  in
  let%map () = unify mono mono' in
  vars

and add_rec_bindings l =
  let open State.Result.Let_syntax in
  let%bind bindings =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
           let%map _, b = gen_binding_ty_vars ~initial_vars:[] ~binding in
           (b, value_restriction expr)))
  in
  let act_on_var var mono =
    let%bind current = lookup_var (Qualified.Unqualified var) in
    let mono' = mono_of_poly_no_inst current in
    let%bind () = unify mono mono' in
    add_var var (Mono mono)
  in
  let%bind vars_list =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
           let%bind mono = mono_of_expr expr in
           let%map _, vars =
             process_binding ~act_on_var ~initial_vars:[] ~binding ~mono
           in
           vars))
  in
  let%map () =
    List.map bindings ~f:(fun (inner, v) ->
        match v with
        | false -> State.Result.all_unit (List.map inner ~f:gen_var)
        | true -> return ())
    |> State.Result.all_unit
  in
  let bindings = List.unzip bindings |> fst in
  List.concat [ vars_list; bindings ]

and mono_of_field expr field ~mut =
  let open State.Result.Let_syntax in
  let%bind type_proof, muta, poly = lookup_field field in
  let%bind () =
    match (mut, muta) with
    | true, `Immutable ->
        State.Result.error
          [%message
            "Field needs to be mutable" (field : Lowercase.t Qualified.t)]
    | _ -> return ()
  in
  let%bind named_poly = Named type_proof |> gen |> State.map ~f:Result.return in
  let%bind monos =
    inst_many [ named_poly; poly ] |> State.map ~f:Result.return
  in
  let type_proof, mono =
    match monos with
    | [ Named type_proof; mono ] -> (type_proof, mono)
    | _ -> assert false
  in
  let%bind expr_mono = mono_of_expr expr in
  let%bind () = unify expr_mono (Named type_proof) in
  let%map mono = apply_substs mono in
  mono

and mono_of_expr expr =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node node -> mono_of_node node
  | Ref expr ->
      let%bind mono = mono_of_expr expr in
      let%map mono = apply_substs mono in
      Reference mono
  | Deref expr ->
      let%bind tyvar = gen_ty_var in
      let%bind mono = mono_of_expr expr in
      let%map () = unify mono (Reference tyvar) in
      Reference mono
  | Field_access (expr, field) -> mono_of_field expr field ~mut:false
  | Field_set (expr1, field, expr2) ->
      let%bind field_mono = mono_of_field expr1 field ~mut:true in
      let%bind rhs_mono = mono_of_expr expr2 in
      let%map () = unify field_mono rhs_mono in
      Named unit_type
  | If (pred, then_, else_) ->
      let%bind pred_mono = mono_of_expr pred in
      let%bind then_mono = mono_of_expr then_ in
      let%bind else_mono = mono_of_expr else_ in
      let%bind () = unify pred_mono (Named bool_type) in
      let%bind () = unify then_mono else_mono in
      apply_substs then_mono
  | App (func, arg) ->
      let%bind func_mono = mono_of_expr func in
      let%bind arg_mono = mono_of_expr arg in
      let%bind res_mono = gen_ty_var in
      let%bind () = unify func_mono (Lambda (arg_mono, res_mono)) in
      apply_substs res_mono
  | Typed (expr, ty) -> (
      let%bind mono = mono_of_expr expr in
      match ty.type_expr with
      | None -> apply_substs mono
      | Some ty ->
          let%bind ty_mono = type_of_type_expr ty in
          let%bind () = unify mono ty_mono in
          apply_substs mono)
  | Let_in (Ast.Nonrec (binding, expr1), expr2) ->
      let%bind vars = add_nonrec_bindings ~binding ~expr:expr1 in
      let%bind res = mono_of_expr expr2 in
      let%bind () = State.Result.all_unit (List.map vars ~f:pop_var) in
      apply_substs res
  | Let_in (Ast.Rec l, expr2) ->
      let%bind vars = add_rec_bindings l in
      let%bind res = mono_of_expr expr2 in
      let%bind () =
        State.Result.all_unit
          (List.map vars ~f:(fun vars ->
               State.Result.all_unit (List.map (List.rev vars) ~f:pop_var)))
      in

      apply_substs res
  | Match (expr1, cases) -> (
      let%bind mono1 = mono_of_expr expr1 in
      match%bind
        State.Result.all
          (List.map cases ~f:(fun (binding, expr2) ->
               mono_of_binding_typed ~binding ~mono1 ~expr2 ~generalize:false
                 ~value_restriction:false))
      with
      | [] -> State.Result.error [%message "Empty match"]
      | mono :: _ as l ->
          let%bind () = State.Result.all_unit (List.map l ~f:(unify mono)) in
          apply_substs mono)
  | Lambda (binding, body) ->
      let%bind var = gen_ty_var in
      let%bind res_type =
        mono_of_binding_typed ~binding ~mono1:var ~expr2:body ~generalize:false
          ~value_restriction:false
      in
      let%bind var = apply_substs var in
      let%map res_type = apply_substs res_type in
      Lambda (var, res_type)

let process_let_def (let_def : Ast.let_def) =
  let open State.Result.Let_syntax in
  let%bind () =
    match let_def with
    | Ast.Rec l -> add_rec_bindings l >>| ignore
    | Ast.Nonrec (binding, expr) ->
        add_nonrec_bindings ~binding ~expr >>| ignore
  in
  let%bind state = State.Result.get in
  State.Result.put { state with mono_ufds = Mono_ufds.empty }

let rec unify_module_bindings ~(signature : module_bindings)
    ~(definition : module_bindings) =
  let open State.Result.Let_syntax in
  let%bind joined_vars =
    try
      return
      @@ Lowercase.Map.merge signature.toplevel_vars definition.toplevel_vars
           ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with Field_left_only key ->
      State.Result.error
        [%message "Value in signature not in definition" (key : Lowercase.t)]
  in
  let%bind () =
    Lowercase.Map.fold joined_vars ~init:(return ())
      ~f:(fun ~key:_ ~data:(left, right) acc ->
        let%bind () = acc in
        let _, sig_val = List.hd_exn left |> split_poly in
        let _, def_val = List.hd_exn right |> split_poly in
        unify_less_general sig_val def_val)
  in
  let%bind joined_type_constructors =
    try
      return
      @@ Lowercase.Map.merge signature.toplevel_type_constructors
           definition.toplevel_type_constructors ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with Field_left_only key ->
      State.Result.error
        [%message
          "Type constructor in signature not in definition" (key : Lowercase.t)]
  in
  let%bind type_constructors =
    Lowercase.Map.fold joined_type_constructors
      ~init:(return Lowercase.Map.empty) ~f:(fun ~key ~data:(left, right) acc ->
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
        Lowercase.Map.add_exn ~key ~data:right acc)
  in
  let%bind joined_modules =
    try
      return
      @@ Uppercase.Map.merge signature.toplevel_modules
           definition.toplevel_modules ~f:(fun ~key -> function
           | `Both x -> Some x
           | `Left _ -> raise (Field_left_only key)
           | `Right _ -> None)
    with Field_left_only key ->
      State.Result.error
        [%message "Module in signature not in definition" (key : Uppercase.t)]
  in
  let%bind () =
    Uppercase.Map.fold joined_modules ~init:(return ())
      ~f:(fun ~key:_ ~data:(left, right) acc ->
        let%bind () = acc in
        unify_module_bindings ~signature:left ~definition:right >>| ignore)
  in
  return { signature with toplevel_type_constructors = type_constructors }

let rec process_module_named (name : Uppercase.t Qualified.t) =
  let open State.Result.Let_syntax in
  let qualifications = Qualified.full_qualifications name in
  let%bind other = find_module_binding qualifications in
  set_current_module_binding other

and process_struct (toplevels : Ast.toplevel list) =
  State.Result.all_unit @@ List.map ~f:process_toplevel toplevels

and process_functor_app (f : Uppercase.t Qualified.t) (a : Ast.module_def list)
    =
  let _ = (f, a) in
  failwith "TODO"

and process_sig (toplevel_types : Ast.module_sig) =
  State.Result.all_unit @@ List.map ~f:process_toplevel_type toplevel_types

and process_module_def (d : Ast.module_def) =
  match d with
  | Ast.Struct s -> process_struct s
  | Ast.Named f -> process_module_named f
  | Ast.Functor_app (f, a) -> process_functor_app f a
  | Ast.Module_typed (s, si) ->
      let open State.Result.Let_syntax in
      let%bind () = process_sig si in
      let%bind name, signature = pop_module in
      let%bind () = change_to_new_module name in
      let%bind () = process_module_def s in
      let%bind name, definition = pop_module in
      let%bind module_ = unify_module_bindings ~signature ~definition in
      change_to_module name module_

and process_module_description _ = failwith "TODO"

and process_module
    ~(module_description : Ast.module_sig option Ast.module_description)
    ~(module_def : Ast.module_def) =
  let open State.Result.Let_syntax in
  let%bind () = change_to_new_module module_description.module_name in
  match module_description with
  | { module_name = _; functor_args = []; module_sig } ->
      let%bind sig_module_bindings =
        match module_sig with
        | Some module_sig ->
            let%bind () = process_sig module_sig in
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
            unify_module_bindings ~signature:sig_module_bindings
              ~definition:def_module_bindings
        | None -> return def_module_bindings
      in
      add_module ~name:current_name ~module_bindings
  | _ -> failwith "TODO"

and process_toplevel_type (toplevel_type : Ast.toplevel_type) =
  match toplevel_type with
  | Ast.Sig_binding _ -> failwith "TODO"
  | Ast.Sig_module module_description ->
      process_module_description module_description
  | Ast.Sig_type_def _ -> failwith "TODO"

and process_toplevel (toplevel : Ast.toplevel) =
  match toplevel with
  | Ast.Type_def type_def -> process_type_def type_def
  | Ast.Let let_def -> process_let_def let_def
  | Ast.Module_def { module_description; module_def } ->
      process_module ~module_description ~module_def

and process_toplevel_list (l : Ast.t) =
  let open State.Result.Let_syntax in
  let%bind () = State.Result.all_unit (List.map l ~f:process_toplevel) in
  let%map state = State.Result.get in
  state.current_module_binding

let rec replace_type_name ~type_name (mono : mono) =
  match mono with
  | TyVar _ | Weak _ -> mono
  | Lambda (a, b) ->
      Lambda (replace_type_name ~type_name a, replace_type_name ~type_name b)
  | Tuple l -> Tuple (List.map l ~f:(replace_type_name ~type_name))
  | Reference x -> Reference (replace_type_name ~type_name x)
  | Named type_proof -> Named (replace_type_name_proof ~type_name type_proof)

and replace_type_name_proof ~type_name type_proof =
  { type_proof with type_name }

let rec show_mono_def (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | Named { type_id; _ } -> (
      match%bind lookup_type_map type_id with
      | _, _, { type_id = t'; _ } when phys_equal t' type_id -> show_mono mono
      | _, user_type, _ -> (
          match%bind show_user_type user_type with
          | Some s -> return s
          | None -> show_mono mono))
  | Weak s -> return [%string "weak %{s}"]
  | TyVar s -> return s
  | Lambda _ | Tuple _ | Reference _ -> show_mono mono

and show_user_type (user_type : user_type) =
  let open State.Result.Let_syntax in
  match user_type with
  | Abstract -> return None
  | Record fields ->
      [%sexp
        (fields : (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t)]
      |> Sexp.to_string_hum |> Option.some |> return
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

let rec show_module_bindings
    { toplevel_vars; toplevel_type_constructors; toplevel_modules; _ } =
  let open State.Result.Let_syntax in
  let%bind type_strings =
    Lowercase.Map.to_alist toplevel_type_constructors
    |> List.map ~f:(fun (type_name, type_id) ->
           let%bind args, user_type, _ = lookup_type_map type_id in
           let prefix_str =
             match args with
             | Some args -> show_type_constructor_arg args ^ " "
             | None -> ""
           in
           let%map rhs = show_user_type user_type in
           match rhs with
           | Some mono_s ->
               [%string "type %{prefix_str}%{type_name} = %{mono_s}"]
           | None -> [%string "type %{prefix_str}%{type_name}"])
    |> State.Result.all
  in
  let%bind var_strings =
    Lowercase.Map.to_alist toplevel_vars
    |> List.map ~f:(fun (v, poly_list) ->
           let%bind poly =
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
    Uppercase.Map.to_alist toplevel_modules
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
