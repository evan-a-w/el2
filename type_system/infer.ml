open! Core
open! Shared
open! Frontend

type variance_map = Variance.t Lowercase.Map.t
[@@deriving sexp, equal, hash, compare]

type type_constructor_arg =
  | Tuple_arg of (Variance.t * Lowercase.t) list
  | Single_arg of Variance.t * Lowercase.t
[@@deriving sexp, equal, hash, compare]

type type_constructor =
  type_constructor_arg * Lowercase.t * mono
  (* replace bound variables in type_constructor_arg with new TyVars when using this mono *)
[@@deriving sexp, equal, hash, compare]

(* can't generalize the type of values (ie. things that arent just straight up a function,
   incl. lambdas)*)
(* BUT always safe to generalize variables that are only used covariantly *)
(* a use of a type variable is instantiating a value of type equal to the variable or a
   type parameterised by that variable.
   Can check if type is parameterised by the variable simply by mapping over the type
   and finding tyvars.
   This should probably be cached. *)
(* Variances of record fields is covariant if not mutable, invariant if mutable *)
(* Variances of Enum is the combination of all underlying types *)
and mono =
  | Recursive_constructor
  | Abstract of Lowercase.t Qualified.t * mono option
  (* keep track of the path and arg for equality *)
  | TyVar of Lowercase.t
  | Lambda of mono * mono
  | Tuple of mono list
  | Record of (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t
  | Enum of (Uppercase.t * mono option) List.t
  | Pointer of mono
[@@deriving sexp, equal, hash, compare]

type poly = Mono of mono | Forall of Lowercase.t * poly
[@@deriving sexp, equal, hash, compare]

module Mono_ufds = Ufds.Make (struct
  type t = mono [@@deriving sexp, equal, hash, compare]
end)

module Module_path = Qualified.Make (struct
  type arg = Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

type module_bindings = {
  toplevel_vars : mono Lowercase.Map.t;
  toplevel_records : (Lowercase.Set.t * mono) list;
  toplevel_type_constructors : type_constructor Lowercase.Map.t;
  toplevel_types : mono Lowercase.Map.t;
  toplevel_modules : module_bindings Uppercase.Map.t;
  opened_modules : module_bindings List.t;
}
[@@deriving sexp, equal, hash, compare, fields]

let empty_module_bindngs =
  {
    toplevel_vars = Lowercase.Map.empty;
    toplevel_records = [];
    toplevel_type_constructors = Lowercase.Map.empty;
    toplevel_types = Lowercase.Map.empty;
    toplevel_modules = Uppercase.Map.empty;
    opened_modules = [];
  }

type state = {
  mono_ufds : Mono_ufds.t;
  current_module_binding : module_bindings;
  current_qualification : Uppercase.t list;
  (* type var in code -> type var *)
  type_var_map : Lowercase.t List.t Lowercase.Map.t;
  symbol_n : int;
}
[@@deriving sexp, equal, compare, fields]

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let add_type_constructor arg name mono =
  let open State.Let_syntax in
  let%bind state = State.get in
  let data = (arg, name, mono) in
  let toplevel_type_constructors =
    Lowercase.Map.set state.current_module_binding.toplevel_type_constructors
      ~key:name ~data
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_type_constructors }
  in
  State.Result.put { state with current_module_binding }

let empty_state =
  {
    mono_ufds = Mono_ufds.empty;
    current_module_binding = empty_module_bindngs;
    current_qualification = [];
    type_var_map = Lowercase.Map.empty;
    symbol_n = 0;
  }

let gensym : string state_m =
  let open State.Let_syntax in
  let%bind state = State.get in
  let s = state.symbol_n in
  let%bind () = State.put { state with symbol_n = s + 1 } in
  let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
  let s = String.make 1 letter ^ Int.to_string (s / 26) in
  return s

let push_type_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let%bind var = gensym in
  let type_var_map =
    Lowercase.Map.add_multi state.type_var_map ~key:name ~data:var
  in
  let%bind () = State.put { state with type_var_map } in
  return var

let pop_type_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let type_var_map = Lowercase.Map.remove_multi state.type_var_map name in
  State.put { state with type_var_map }

let add_type name mono =
  let open State.Let_syntax in
  let%bind state = State.get in
  let toplevel_types =
    Lowercase.Map.set state.current_module_binding.toplevel_types ~key:name
      ~data:mono
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_types }
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
(*   | Pointer mono -> calculate_variance mono *)
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

let find mono =
  let%bind.State state = State.get in
  let mono, mono_ufds = Mono_ufds.find state.mono_ufds mono in
  let%map.State () = State.put { state with mono_ufds } in
  mono

let union mono1 mono2 =
  let%bind.State state = State.get in
  let mono_ufds = Mono_ufds.union state.mono_ufds mono1 mono2 in
  State.put { state with mono_ufds }

let rec search_modules :
    type a.
    module_bindings ->
    qualifications:Qualified.qualifications ->
    search_for:(module_bindings -> a option) ->
    a option =
 fun module_bindings ~qualifications ~(search_for : module_bindings -> a option) ->
  match qualifications with
  | [] -> search_for module_bindings
  | name :: qualifications -> (
      let open Option.Let_syntax in
      let first =
        Uppercase.Map.find module_bindings.toplevel_modules name
        >>= search_modules ~qualifications ~search_for
      in
      match first with
      | Some _ -> first
      | None ->
          List.find_map module_bindings.opened_modules
            ~f:(search_modules ~qualifications ~search_for))

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
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

let lookup_type qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  (* let type_var_type = *)
  (*   match qualifications with *)
  (*   | [] -> *)
  (*       Option.bind (Lowercase.Map.find state.type_var_map type_name) ~f:List.hd *)
  (*       |> Option.map ~f:(fun x -> TyVar x) *)
  (*   | _ -> None *)
  (* in *)
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_types type_name)
  in
  State.Result.return (Option.value res ~default:(TyVar type_name))
(* match Option.first_some type_var_type res with *)
(* | Some x -> State.Result.return x *)
(* | None -> *)
(*     State.Result.error *)
(*       [%message "type not found" (qualified_name : Lowercase.t Qualified.t)] *)

let rec map_ty_vars ~f (mono : mono) =
  match mono with
  | TyVar m -> Option.value (f m) ~default:mono
  | Lambda (a, b) -> Lambda (map_ty_vars ~f a, map_ty_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_ty_vars ~f))
  | Record l ->
      Record (List.Assoc.map l ~f:(Tuple2.map_fst ~f:(map_ty_vars ~f)))
  | Enum l -> Enum (List.Assoc.map l ~f:(Option.map ~f:(map_ty_vars ~f)))
  | Pointer x -> Pointer (map_ty_vars ~f x)
  | Abstract _ | Recursive_constructor -> mono

let iter_ty_vars ~f mono =
  ignore
    (map_ty_vars mono ~f:(fun x ->
         f x;
         None))

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> List.map ~f:snd l |> Lowercase.Set.of_list
  | Single_arg (_, x) -> Lowercase.Set.singleton x

let free_ty_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_ty_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x);
  !set

let replace_ty_vars ~replacement_map =
  map_ty_vars ~f:(Lowercase.Map.find replacement_map)

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
      Pointer mono
  | Ast.Type_expr.Tuple l ->
      let%map monos = State.Result.all (List.map l ~f:type_of_type_expr) in
      Tuple monos
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (first, second) ->
      let%bind constructor_arg, _, mono = lookup_type_constructor second in
      let%bind arg = type_of_type_expr first in
      let mono =
        match mono with
        | Abstract (name, _) -> Abstract (name, Some arg)
        | _ -> mono
      in
      let vars =
        match constructor_arg with
        | Single_arg (_, x) -> [ x ]
        | Tuple_arg l -> List.unzip l |> snd
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
      replace_ty_vars ~replacement_map mono

let type_of_type_def_lit (type_def_lit : Ast.Type_def_lit.t) =
  let open State.Result.Let_syntax in
  match type_def_lit with
  | Ast.Type_def_lit.Type_expr type_expr -> type_of_type_expr type_expr
  | Ast.Type_def_lit.Record l ->
      let%map monos =
        List.map l ~f:(fun (name, (type_expr, mutability)) ->
            let%map mono = type_of_type_expr type_expr in
            (name, (mono, mutability)))
        |> State.Result.all
      in
      Record monos
  | Ast.Type_def_lit.Enum l ->
      let%map monos =
        List.map l ~f:(fun (name, type_expr) ->
            let%map mono =
              match type_expr with
              | Some type_expr -> type_of_type_expr type_expr >>| Option.some
              | None -> return None
            in
            (name, mono))
        |> State.Result.all
      in
      Enum monos

let process_type_def
    ({ type_name; type_def; ast_tags = _ } :
      Ast.Type_def_lit.t Ast.type_description) =
  let open State.Result.Let_syntax in
  match type_name with
  | Ast.Type_binding.Mono type_name ->
      let%bind mono = type_of_type_def_lit type_def in
      let rhs_ty_vars = free_ty_vars mono in
      let%bind () =
        match Lowercase.Set.length rhs_ty_vars with
        | 0 -> State.Result.return ()
        | _ ->
            State.Result.error
              [%message
                "type definition has free type variables"
                  (mono : mono)
                  ~vars:(Lowercase.Set.to_list rhs_ty_vars : Lowercase.t list)
                  (type_name : Lowercase.t)]
      in
      add_type type_name mono
  | Ast.Type_binding.Poly (arg, type_name) -> (
      let constructor_arg =
        match arg with
        | Ast.Type_binding.Single (v, l) -> Single_arg (v, l)
        | Ast.Type_binding.Tuple l -> Tuple_arg l
      in
      let lhs_ty_vars = constructor_arg_free_ty_vars constructor_arg in
      let%bind () =
        add_type_constructor constructor_arg type_name Recursive_constructor
      in
      let%bind mono = type_of_type_def_lit type_def in
      let rhs_ty_vars = free_ty_vars mono in
      match Lowercase.Set.equal lhs_ty_vars rhs_ty_vars with
      | true -> add_type_constructor constructor_arg type_name mono
      | false ->
          State.Result.error
            [%message
              "Type vars not equal in type def"
                (type_name : Lowercase.t)
                (mono : mono)
                (lhs_ty_vars : Lowercase.Set.t)
                (rhs_ty_vars : Lowercase.Set.t)])

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

let gen (mono : mono) : poly state_m =
  Lowercase.Set.fold ~init:(Mono mono) ~f:(fun acc x -> Forall (x, acc))
  @@ free_ty_vars mono
  |> State.return

let unify mono1 mono2 =
  (* let open State.Result in *)
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  match (mono1, mono2) with _ -> failwith "TODO"
