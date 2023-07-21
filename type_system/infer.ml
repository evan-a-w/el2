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
and type_proof = Lowercase.t Qualified.t * mono Lowercase.Map.t * int
[@@deriving sexp, equal, hash, compare]

and mono =
  (* name and type args *)
  | Recursive_constructor of type_proof
  | Abstract of type_proof
  | Weak of Lowercase.t
  (* keep track of the path and arg for equality *)
  | TyVar of Lowercase.t
  | Lambda of mono * mono
  | Tuple of mono list
  | Record of
      type_proof * (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t
  | Enum of type_proof * (Uppercase.t * mono option) List.t
  | Pointer of mono
[@@deriving sexp, equal, hash, compare]

type poly = Mono of mono | Forall of Lowercase.t * poly
[@@deriving sexp, equal, hash, compare, variants]

let rec split_poly = function
  | Mono m -> (Lowercase.Set.empty, m)
  | Forall (a, b) ->
      let set, m = split_poly b in
      (Lowercase.Set.add set a, m)

module Mono_ufds = Ufds.Make (struct
  type t = mono [@@deriving sexp, equal, hash, compare]
end)

module Module_path = Qualified.Make (struct
  type arg = Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

type module_bindings = {
  toplevel_vars : poly list Lowercase.Map.t;
  toplevel_records : (poly Lowercase.Map.t * poly) Lowercase.Set.Map.t;
  toplevel_constructors : (poly option * poly) Uppercase.Map.t;
  toplevel_type_constructors : type_constructor Lowercase.Map.t;
  toplevel_types : mono Lowercase.Map.t;
  toplevel_modules : module_bindings Uppercase.Map.t;
  opened_modules : module_bindings List.t;
}
[@@deriving sexp, equal, hash, compare, fields]

let empty_module_bindngs =
  {
    toplevel_vars = Lowercase.Map.empty;
    toplevel_records = Lowercase.Set.Map.empty;
    toplevel_constructors = Uppercase.Map.empty;
    toplevel_type_constructors = Lowercase.Map.empty;
    toplevel_types = Lowercase.Map.empty;
    toplevel_modules = Uppercase.Map.empty;
    opened_modules = [];
  }

type state = {
  mono_ufds : Mono_ufds.t;
  current_module_binding : module_bindings;
  current_qualification : Uppercase.t list;
  symbol_n : int;
}
[@@deriving sexp, equal, compare, fields]

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let operate_on_toplevel_type_constructors arg name mono ~f =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = (arg, name, mono) in
  let%bind toplevel_type_constructors =
    (f state.current_module_binding.toplevel_type_constructors ~key:name ~data
      : _ state_result_m)
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_type_constructors }
  in
  State.Result.put { state with current_module_binding }

let add_type_constructor arg name mono =
  operate_on_toplevel_type_constructors arg name mono
    ~f:(fun toplevel_type_constructors ~key ~data ->
      match Lowercase.Map.add toplevel_type_constructors ~key ~data with
      | `Ok m -> State.Result.return m
      | `Duplicate ->
          State.Result.error
            [%message "Duplicate type constructor" (name : Lowercase.t)])

let set_type_constructor arg name mono =
  operate_on_toplevel_type_constructors arg name mono
    ~f:(fun toplevel_type_constructors ~key ~data ->
      State.Result.return
      @@ Lowercase.Map.set toplevel_type_constructors ~key ~data)

let empty_state =
  {
    mono_ufds = Mono_ufds.empty;
    current_module_binding = empty_module_bindngs;
    current_qualification = [];
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

let print_ufds_map : unit state_result_m =
  let open State.Result.Let_syntax in
  let%map state = State.Result.get in
  print_s [%message (state.mono_ufds : Mono_ufds.t)]

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
  let type_var_type =
    match qualifications with [] -> Some (TyVar type_name) | _ -> None
  in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_types type_name)
  in
  match Option.first_some res type_var_type with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

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

let rec map_ty_vars ~f (mono : mono) =
  match mono with
  | TyVar m -> Option.value (f m) ~default:mono
  | Weak _ -> mono
  | Lambda (a, b) -> Lambda (map_ty_vars ~f a, map_ty_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_ty_vars ~f))
  | Record (type_proof, l) ->
      Record
        ( map_type_proof ~f type_proof,
          List.Assoc.map l ~f:(Tuple2.map_fst ~f:(map_ty_vars ~f)) )
  | Enum (type_proof, l) ->
      let l = List.Assoc.map l ~f:(Option.map ~f:(map_ty_vars ~f)) in
      Enum (map_type_proof ~f type_proof, l)
  | Pointer x -> Pointer (map_ty_vars ~f x)
  | Recursive_constructor type_proof ->
      Recursive_constructor (map_type_proof ~f type_proof)
  | Abstract type_proof -> Abstract (map_type_proof ~f type_proof)

and map_type_proof ~f (name, map, num_unfold) =
  (name, Lowercase.Map.map map ~f:(map_ty_vars ~f), num_unfold)

let make_weak mono = map_ty_vars mono ~f:(fun x -> Some (Weak x))

let iter_ty_vars ~f mono =
  ignore
    (map_ty_vars mono ~f:(fun x ->
         f x;
         None))

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> snd @@ List.unzip l
  | Single_arg (_, x) -> [ x ]

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

let gen (mono : mono) : poly state_m =
  free_ty_vars mono
  |> Lowercase.Set.fold ~init:(Mono mono) ~f:(fun acc var -> Forall (var, acc))
  |> State.return

let poly_of_mono mono ~generalize =
  if generalize then gen mono else State.return @@ Mono (make_weak mono)

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

let add_record field_map poly : _ state_result_m =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let field_set =
    Lowercase.Map.fold field_map ~init:Lowercase.Set.empty
      ~f:(fun ~key ~data:_ acc -> Lowercase.Set.add acc key)
  in
  match
    Lowercase.Set.Map.add state.current_module_binding.toplevel_records
      ~key:field_set ~data:(field_map, poly)
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

let type_proof_of_monos ~type_name monos num =
  let free_var_set =
    List.fold monos ~init:Lowercase.Set.empty ~f:(fun acc mono ->
        Lowercase.Set.union acc (free_ty_vars mono))
  in
  let free_var_map =
    Lowercase.Set.fold free_var_set ~init:Lowercase.Map.empty ~f:(fun acc x ->
        Lowercase.Map.add_exn acc ~key:x ~data:(TyVar x))
  in
  (type_name, free_var_map, num)

let type_of_type_def_lit ~type_name ~update_records_and_constructors
    (type_def_lit : Ast.Type_def_lit.t) =
  let open State.Result.Let_syntax in
  match type_def_lit with
  | Ast.Type_def_lit.Type_expr type_expr -> type_of_type_expr type_expr
  | Ast.Type_def_lit.Record l ->
      let%bind monos =
        List.map l ~f:(fun (name, (type_expr, mutability)) ->
            let%map mono = type_of_type_expr type_expr in
            (name, (mono, mutability)))
        |> State.Result.all
      in
      let type_proof =
        type_proof_of_monos ~type_name
          (List.map monos ~f:(Fn.compose fst snd))
          1
      in
      let mono = Record (type_proof, monos) in
      let%bind poly = State.map (gen mono) ~f:Result.return in
      let%map () =
        match update_records_and_constructors with
        | false -> return ()
        | true ->
            let%bind polys =
              State.Result.all
                (List.map monos ~f:(fun (field, (mono, _)) ->
                     let%map.State poly = gen mono in
                     Ok (field, poly)))
            in
            let field_map =
              List.fold polys ~init:Lowercase.Map.empty
                ~f:(fun acc (field, poly) ->
                  Lowercase.Map.add_exn acc ~key:field ~data:poly)
            in
            add_record field_map poly
      in
      mono
  | Ast.Type_def_lit.Enum l ->
      let%bind monos =
        List.map l ~f:(fun (name, type_expr) ->
            let%map mono =
              match type_expr with
              | Some type_expr -> type_of_type_expr type_expr >>| Option.some
              | None -> return None
            in
            (name, mono))
        |> State.Result.all
      in
      let monos' = List.filter_map monos ~f:(fun (_, mono) -> mono) in
      let type_proof = type_proof_of_monos ~type_name monos' 1 in
      let mono = Enum (type_proof, monos) in
      let%bind poly = State.map (gen mono) ~f:Result.return in
      let%map () =
        State.Result.all_unit
        @@ List.map monos ~f:(fun (x, mono_option) ->
               if update_records_and_constructors then
                 let%bind poly_option =
                   match mono_option with
                   | Some mono -> State.map (gen mono) ~f:(fun x -> Ok (Some x))
                   | None -> return None
                 in
                 add_constructor x poly_option poly
               else return ())
      in
      mono

let process_type_def
    ({ type_name; type_def; ast_tags = _ } :
      Ast.Type_def_lit.t Ast.type_description) =
  let open State.Result.Let_syntax in
  match type_name with
  | Ast.Type_binding.Mono type_name ->
      let%bind mono =
        type_of_type_def_lit ~type_name:(Unqualified type_name)
          ~update_records_and_constructors:true type_def
      in
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
      let lhs_ty_vars =
        List.fold lhs_ty_vars ~init:Lowercase.Map.empty ~f:(fun acc key ->
            Lowercase.Map.add_exn acc ~key ~data:(TyVar key))
      in
      let recursive_constructor =
        Recursive_constructor (Qualified.Unqualified type_name, lhs_ty_vars, 1)
      in
      let%bind () =
        add_type_constructor constructor_arg type_name recursive_constructor
      in
      let%bind mono =
        type_of_type_def_lit ~type_name:(Qualified.Unqualified type_name)
          ~update_records_and_constructors:true type_def
      in
      let rhs_ty_vars = free_ty_vars mono in
      let lhs_ty_vars = Lowercase.Map.key_set lhs_ty_vars |> Obj.magic in
      match Lowercase.Set.equal lhs_ty_vars rhs_ty_vars with
      | true -> set_type_constructor constructor_arg type_name mono
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

let inst_result x = State.map (inst x) ~f:Result.return

let unification_error mono1 mono2 =
  State.Result.error
    [%message
      "failed to unify types" ~first:(mono1 : mono) ~second:(mono2 : mono)]

let type_of_constructor constructor =
  let open State.Result.Let_syntax in
  let%bind arg, poly_res = lookup_constructor constructor in
  let%bind mono_res = inst_result poly_res in
  match arg with
  | None -> return mono_res
  | Some poly_arg ->
      let%map mono_arg = inst_result poly_arg in
      Lambda (mono_arg, mono_res)

let type_recursion_level ~unification_error mono =
  let open State.Result.Let_syntax in
  match mono with
  | Recursive_constructor (_, _, level) -> return level
  | Record ((_, _, level), _) -> return level
  | Enum ((_, _, level), _) -> return level
  | _ -> unification_error ()

let fix_recursive_constructor ~unification_error mono1 mono2 =
  let open State.Result.Let_syntax in
  let inner (name, replacement_map, _) mono =
    let%bind _, _, type_ = lookup_type_constructor name in
    let%map poly = State.map (gen type_) ~f:Result.return in
    let _, mono' = split_poly poly in
    let mono' = replace_ty_vars ~replacement_map mono' in
    (mono', mono)
  in
  match (mono1, mono2) with
  | Recursive_constructor _, Recursive_constructor _ -> return (mono1, mono2)
  | Recursive_constructor arg, mono ->
      let%map left, right = inner arg mono in
      (left, right)
  | mono, Recursive_constructor arg ->
      let%map left, right = inner arg mono in
      (right, left)
  | _ -> return (mono1, mono2)

let occurs_check a mono =
  let open State.Result.Let_syntax in
  let free_vars = free_ty_vars mono in
  match Lowercase.Set.mem free_vars a with
  | true ->
      State.Result.error
        [%message "occurs check failed" (a : Lowercase.t) (mono : mono)]
  | false -> return ()

let rec unify mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  let unification_error () = unification_error mono1 mono2 in
  let%bind mono1, mono2 =
    fix_recursive_constructor ~unification_error mono1 mono2
  in
  match (mono1, mono2) with
  (* this should only happen with recursive calls from enum because
     there are no toplevel recursive constructors *)
  | ( Recursive_constructor (name1, rep1, _),
      Recursive_constructor (name2, rep2, _) )
  | Abstract (name1, rep1, _), Abstract (name2, rep2, _) -> (
      let monos1 = Lowercase.Map.data rep1 in
      let monos2 = Lowercase.Map.data rep2 in
      match Qualified.equal Lowercase.equal name1 name2 with
      | true -> unify_lists monos1 monos2
      | false ->
          State.Result.error
            [%message
              "recursive constructors not equal"
                (name1 : Lowercase.t Qualified.t)
                (name2 : Lowercase.t Qualified.t)])
  | Recursive_constructor _, _ | _, Recursive_constructor _ ->
      unification_error ()
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
  | Pointer x, Pointer y -> unify x y
  | Lambda (x1, x2), Lambda (y1, y2) ->
      let%bind () = unify x1 y1 in
      unify x2 y2
  | Tuple l1, Tuple l2 -> unify_lists unification_error l1 l2
  | Record l1, Record l2 ->
      let%bind zipped =
        match List.zip l1 l2 with
        | Unequal_lengths -> unification_error ()
        | Ok zipped -> return zipped
      in
      let f ((field1, (mono1, mut1)), (field2, (mono2, mut2))) =
        match (String.equal field1 field2, mut1, mut2) with
        | true, `Mutable, `Mutable | true, `Immutable, `Immutable ->
            unify mono1 mono2
        | _ -> unification_error ()
      in
      State.Result.all_unit (List.map zipped ~f)
  | Enum l1, Enum l2 ->
      let%bind zipped =
        match List.zip l1 l2 with
        | Unequal_lengths -> unification_error ()
        | Ok zipped -> return zipped
      in
      let f ((field1, mono1), (field2, mono2)) =
        match String.equal field1 field2 with
        | false -> unification_error ()
        | true -> (
            match (mono1, mono2) with
            | Some mono1, Some mono2 -> unify mono1 mono2
            | None, None -> State.Result.return ()
            | Some _, None | None, Some _ -> unification_error ())
      in
      State.Result.all_unit (List.map zipped ~f)
  | _ -> unification_error ()

and unify_lists unification_error l1 l2 =
  let open State.Result.Let_syntax in
  let%bind zipped =
    match List.zip l1 l2 with
    | Unequal_lengths -> unification_error ()
    | Ok zipped -> return zipped
  in
  let f (mono1, mono2) = unify mono1 mono2 in
  State.Result.all_unit (List.map zipped ~f)

let make_abstract s = Abstract (Qualified.Unqualified s, None)
let int_type = make_abstract "int"
let float_type = make_abstract "float"
let bool_type = make_abstract "bool"
let unit_type = make_abstract "unit"
let string_type = make_abstract "string"
let char_type = make_abstract "char"

(* TODO: modules *)
let open_module (_qualifications : Qualified.qualifications) =
  State.Result.return ()

let pop_module = State.Result.return ()

let split_poly_list l =
  List.fold l ~init:(Lowercase.Set.empty, []) ~f:(fun (set, monos) poly ->
      let new_vars, mono = split_poly poly in
      (Lowercase.Set.union set new_vars, mono :: monos))

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

let make_free_vars_weak mono =
  let free_vars = free_ty_vars mono in
  let replacement_map =
    Lowercase.Set.to_map free_vars ~f:(fun x -> Weak x) |> Obj.magic
  in
  replace_ty_vars ~replacement_map mono

let value_restriction expr = match expr with Lambda _ -> true | _ -> false

let gen_ty_var : _ state_result_m =
  let%map.State sym = gensym in
  Ok (TyVar sym)

let mono_of_literal literal =
  match literal with
  | Ast.Literal.Int _ -> State.Result.return int_type
  | Ast.Literal.Float _ -> State.Result.return float_type
  | Ast.Literal.Bool _ -> State.Result.return bool_type
  | Ast.Literal.Unit -> State.Result.return unit_type
  | Ast.Literal.String _ -> State.Result.return string_type
  | Ast.Literal.Char _ -> State.Result.return char_type

let rec mono_of_node node =
  let open State.Result.Let_syntax in
  match node with
  | Ast.Literal literal -> mono_of_literal literal
  | Ast.Var var_name -> lookup_var var_name >>= inst_result
  | Ast.Tuple qualified_tuple ->
      let qualifications, tuple = Qualified.split qualified_tuple in
      let%bind () = open_module qualifications in
      let%bind l = State.Result.all (List.map tuple ~f:mono_of_expr) in
      let%map () = pop_module in
      Tuple l
  | Ast.Wrapped qualified_expr ->
      let qualifications, expr = Qualified.split qualified_expr in
      let%bind () = open_module qualifications in
      let%bind res = mono_of_expr expr in
      let%map () = pop_module in
      res
  | Ast.Constructor constructor -> type_of_constructor constructor
  | Ast.Record qualified_record ->
      let qualifications, record = Qualified.split qualified_record in
      let%bind () = open_module qualifications in
      let%bind field_map, poly_res =
        lookup_record (Qualified.Unqualified record)
      in
      let%bind mono_res = inst_result poly_res in
      let field_list = Lowercase.Map.to_alist field_map in
      let field_polys = List.map field_list ~f:snd in
      let%bind field_monos =
        State.map (inst_many field_polys) ~f:Result.return
      in
      let field_mono_map =
        List.map2_exn field_list field_monos ~f:(fun (field, _) mono ->
            (field, mono))
        |> Lowercase.Map.of_alist_exn
      in
      let%map () =
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
      mono_res

and process_binding ~(binding : Ast.Binding.t) ~mono ~generalize :
    (poly * Lowercase.t list) state_result_m =
  let open State.Result.Let_syntax in
  match binding with
  | Ast.Binding.Literal l ->
      let%bind binding_mono = mono_of_literal l in
      let%map () = unify binding_mono mono in
      (Mono mono, [])
  | Ast.Binding.Name var ->
      let%bind poly =
        State.map (poly_of_mono ~generalize mono) ~f:Result.return
      in
      let%map () = add_var var poly in
      (poly, [ var ])
  | Ast.Binding.Constructor (constructor, rest) -> (
      let%bind arg, poly = lookup_constructor constructor in
      match (rest, arg) with
      | None, None -> return (poly, [])
      | None, Some arg_type ->
          State.Result.error
            [%message
              "Constructor takes an argument (none given)"
                (constructor : Uppercase.t Qualified.t)
                (arg_type : poly)]
      | Some given, None ->
          State.Result.error
            [%message
              "Constructor takes no argument"
                (constructor : Uppercase.t Qualified.t)
                (given : Ast.Binding.t)]
      | Some binding, Some arg_poly ->
          let%bind mono = inst_result arg_poly in
          let%map _, vars = process_binding ~binding ~mono ~generalize in
          (poly, vars))
  | Ast.Binding.Typed (binding, value_tag) -> (
      let type_expr = value_tag.Ast.Value_tag.type_expr in
      match type_expr with
      | None -> process_binding ~binding ~mono ~generalize
      | Some type_expr ->
          let%bind tagged_mono = type_of_type_expr type_expr in
          let%bind () = unify tagged_mono mono in
          process_binding ~binding ~mono ~generalize)
  | Ast.Binding.Renamed (binding, var) ->
      let%bind poly, vars = process_binding ~binding ~mono ~generalize in
      let%map () = add_var var poly in
      (poly, var :: vars)
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
               process_binding ~binding ~mono ~generalize))
      in
      let polys, vars_list = List.unzip processed_list in
      let vars = List.concat (List.rev vars_list) in
      let free_vars, monos = split_poly_list polys in
      let poly =
        Lowercase.Set.fold free_vars ~init:(Mono (Tuple monos))
          ~f:(fun acc var -> Forall (var, acc))
      in
      let%map () = pop_module in
      (poly, vars)
  | Ast.Binding.Record qualified_map ->
      let%bind field_map, poly = lookup_record qualified_map in
      let%bind mono_searched = inst_result poly in
      let%bind () = unify mono_searched mono in
      let qualifications, record = Qualified.split qualified_map in
      (* | Record of (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t *)
      let%bind () = open_module qualifications in
      let%bind vars_list =
        Lowercase.Map.fold record ~init:(State.Result.return [])
          ~f:(fun ~key:field ~data:binding acc ->
            let%bind vars_list = acc in
            let%bind poly =
              match Lowercase.Map.find field_map field with
              | None ->
                  State.Result.error
                    [%message "Unknown field" (field : Lowercase.t)]
              | Some poly -> State.Result.return poly
            in
            let%bind mono = inst_result poly in
            let%map _, vars = process_binding ~binding ~mono ~generalize in
            vars :: vars_list)
      in
      let res_vars = List.concat (List.rev vars_list) in
      let%map () = pop_module in
      (poly, res_vars)

and mono_of_binding_typed ~(binding : Ast.Binding.t) ~mono1 ~expr2 ~generalize =
  let open State.Result.Let_syntax in
  let%bind _, vars = process_binding ~binding ~mono:mono1 ~generalize in
  let%bind res = mono_of_expr expr2 in
  let%map () = State.Result.all_unit (List.map vars ~f:pop_var) in
  res

and mono_of_binding ~(binding : Ast.Binding.t) ~expr1 ~expr2 ~generalize =
  let%bind.State.Result mono1 = mono_of_expr expr1 in
  mono_of_binding_typed ~binding ~mono1 ~expr2 ~generalize

and mono_of_expr expr =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node node -> mono_of_node node
  | If (pred, then_, else_) ->
      let%bind pred_mono = mono_of_expr pred in
      let%bind then_mono = mono_of_expr then_ in
      let%bind else_mono = mono_of_expr else_ in
      let%bind () = unify pred_mono bool_type in
      let%map () = unify then_mono else_mono in
      then_mono
  | App (func, arg) ->
      let%bind func_mono = mono_of_expr func in
      let%bind arg_mono = mono_of_expr arg in
      let%bind res_mono = gen_ty_var in
      let%map () = unify func_mono (Lambda (arg_mono, res_mono)) in
      res_mono
  | Typed (expr, ty) -> (
      let%bind mono = mono_of_expr expr in
      match ty.type_expr with
      | None -> return mono
      | Some ty ->
          let%bind ty_mono = type_of_type_expr ty in
          let%map () = unify mono ty_mono in
          mono)
  | Let_in (binding, expr1, expr2) ->
      mono_of_binding ~binding ~expr1 ~expr2 ~generalize:true
  | Match (expr1, cases) -> (
      match%bind
        State.Result.all
          (List.map cases ~f:(fun (binding, expr2) ->
               mono_of_binding ~binding ~expr1 ~expr2 ~generalize:false))
      with
      | [] -> State.Result.error [%message "Empty match"]
      | mono :: _ as l ->
          let%map () = State.Result.all_unit (List.map l ~f:(unify mono)) in
          mono)
  | Lambda (binding, body) ->
      let%bind weak_var =
        let%map.State sym = gensym in
        Ok (Weak sym)
      in
      let%map res_type =
        mono_of_binding_typed ~binding ~mono1:weak_var ~expr2:body
          ~generalize:false
      in
      Lambda (weak_var, res_type)

let rec apply_substs (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | Recursive_constructor (name, monos) ->
      let%map monos = State.Result.all (List.map monos ~f:apply_substs) in
      Recursive_constructor (name, monos)
  | Abstract (_, _) | Weak _ | TyVar _ -> State.map (find mono) ~f:Result.return
  | Lambda (a, b) ->
      let%bind a = apply_substs a in
      let%map b = apply_substs b in
      Lambda (a, b)
  | Tuple l ->
      let%map l = State.Result.all (List.map l ~f:apply_substs) in
      Tuple l
  (* | Recursive_constructor l -> *)
  (*     let%map l = State.Result.all (List.map l ~f:apply_substs) in *)
  (*     Recursive_constructor l *)
  | Record m ->
      let%map m =
        State.Result.all
          (List.map m ~f:(fun (field, (mono, mut)) ->
               let%map mono = apply_substs mono in
               (field, (mono, mut))))
      in
      Record m
  | Pointer m ->
      let%map m = apply_substs m in
      Pointer m
  | Enum l ->
      let%map l =
        State.Result.all
          (List.map l ~f:(fun (name, mono) ->
               let%map mono =
                 match mono with
                 | None -> State.Result.return None
                 | Some mono ->
                     let%map mono = apply_substs mono in
                     Some mono
               in
               (name, mono)))
      in
      Enum l
