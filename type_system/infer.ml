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
  | Weak of Lowercase.t
  (* keep track of the path and arg for equality *)
  | TyVar of Lowercase.t
  | Lambda of mono * mono
  | Tuple of mono list
  | Record of (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t
  | Enum of (Uppercase.t * mono option) List.t
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
  | Record l ->
      Record (List.Assoc.map l ~f:(Tuple2.map_fst ~f:(map_ty_vars ~f)))
  | Enum l -> Enum (List.Assoc.map l ~f:(Option.map ~f:(map_ty_vars ~f)))
  | Pointer x -> Pointer (map_ty_vars ~f x)
  | Abstract _ | Recursive_constructor -> mono

let make_weak mono = map_ty_vars mono ~f:(fun x -> Some (Weak x))

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

let gen (mono : mono) : poly state_m =
  free_ty_vars mono
  |> Lowercase.Set.fold ~init:(Mono mono) ~f:(fun acc x -> Forall (x, acc))
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

let type_of_type_def_lit ~update_records_and_constructors
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
      let mono = Record monos in
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
      let mono = Enum monos in
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
        type_of_type_def_lit ~update_records_and_constructors:true type_def
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
      let%bind () =
        add_type_constructor constructor_arg type_name Recursive_constructor
      in
      let%bind mono =
        type_of_type_def_lit ~update_records_and_constructors:true type_def
      in
      let rhs_ty_vars = free_ty_vars mono in
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

let rec unify mono1 mono2 =
  let open State.Result.Let_syntax in
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match (mono1, mono2) with
  (* this should only happen with recursive calls from enum because
     there are no toplevel recursive constructors *)
  | Recursive_constructor, Recursive_constructor -> State.Result.return ()
  | Recursive_constructor, _ | _, Recursive_constructor -> unification_error ()
  | TyVar x, TyVar y when String.equal x y -> State.Result.return ()
  | TyVar _, _ -> union mono2 mono1 |> State.map ~f:Result.return
  | _, TyVar _ -> union mono1 mono2 |> State.map ~f:Result.return
  | Weak x, Weak y when String.equal x y -> State.Result.return ()
  | Weak _, _ -> union mono2 mono1 |> State.map ~f:Result.return
  | _, Weak _ -> union mono1 mono2 |> State.map ~f:Result.return
  | Pointer x, Pointer y -> unify x y
  | Abstract (x, x_arg), Abstract (y, y_arg)
    when Qualified.equal String.equal x y -> (
      match (x_arg, y_arg) with
      | Some x_arg, Some y_arg -> unify x_arg y_arg
      | None, None -> State.Result.return ()
      | Some _, None | None, Some _ -> unification_error ())
  | Lambda (x1, x2), Lambda (y1, y2) ->
      let%bind () = unify x1 y1 in
      unify x2 y2
  | Tuple l1, Tuple l2 ->
      let%bind zipped =
        match List.zip l1 l2 with
        | Unequal_lengths -> unification_error ()
        | Ok zipped -> return zipped
      in
      let f (mono1, mono2) = unify mono1 mono2 in
      State.Result.all_unit (List.map zipped ~f)
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

let poly_of_mono ~free_vars mono =
  Lowercase.Set.fold free_vars ~init:(Mono mono) ~f:(fun acc var ->
      Forall (var, acc))

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

(* let rec poly_of_node node = *)
(*   let open State.Result.Let_syntax in *)
(*   match node with *)
(*   | Ast.Literal (Ast.Literal.Int _) -> State.Result.return @@ mono int_type *)
(*   | Ast.Literal (Ast.Literal.Float _) -> State.Result.return @@ mono float_type *)
(*   | Ast.Literal (Ast.Literal.Bool _) -> State.Result.return @@ mono bool_type *)
(*   | Ast.Literal Ast.Literal.Unit -> State.Result.return @@ mono unit_type *)
(*   | Ast.Literal (Ast.Literal.String _) -> *)
(*       State.Result.return @@ mono string_type *)
(*   | Ast.Literal (Ast.Literal.Char _) -> State.Result.return @@ mono char_type *)
(*   | Ast.Var var_name -> lookup_var var_name *)
(*   | Ast.Tuple qualified_tuple -> *)
(*       let qualifications, tuple = Qualified.split qualified_tuple in *)
(*       let%bind () = open_module qualifications in *)
(*       let%bind l = State.Result.all (List.map tuple ~f:poly_of_expr) in *)
(*       let free_vars, monos = split_poly_list l in *)
(*       let tuple = Tuple (List.rev monos) in *)
(*       let res = poly_of_mono ~free_vars tuple in *)
(*       let%map () = pop_module in *)
(*       res *)
(*   | Ast.Wrapped qualified_expr -> *)
(*       let qualifications, expr = Qualified.split qualified_expr in *)
(*       let%bind () = open_module qualifications in *)
(*       let%bind res = poly_of_expr expr in *)
(*       let%map () = pop_module in *)
(*       res *)
(*   | Ast.Constructor constructor -> ( *)
(*       let%map arg, poly_res = lookup_constructor constructor in *)
(*       match arg with *)
(*       | None -> poly_res *)
(*       | Some poly_arg -> *)
(*           let vars, mono_res = split_poly poly_res in *)
(*           let vars', mono_arg = split_poly poly_arg in *)
(*           let free_vars = Lowercase.Set.union vars vars' in *)
(*           poly_of_mono ~free_vars (Lambda (mono_arg, mono_res))) *)
(*   | Ast.Record qualified_record -> *)
(*       let qualifications, record = Qualified.split qualified_record in *)
(*       let%bind () = open_module qualifications in *)
(*       let%bind field_map, poly_res = *)
(*         lookup_record (Qualified.Unqualified record) *)
(*       in *)
(*       let field_list = Lowercase.Map.to_alist field_map in *)
(*       let field_polys = List.map field_list ~f:snd in *)
(*       let%bind field_monos = *)
(*         State.map (inst_many field_polys) ~f:Result.return *)
(*       in *)
(*       let field_mono_map = *)
(*         List.map2_exn field_list field_monos ~f:(fun (field, _) mono -> *)
(*             (field, mono)) *)
(*         |> Lowercase.Map.of_alist_exn *)
(*       in *)
(*       let%map () = *)
(*         Lowercase.Map.fold record ~init:(State.Result.return ()) *)
(*           ~f:(fun ~key:field ~data:expr acc -> *)
(*             let%bind () = acc in *)
(*             let%bind poly = poly_of_expr expr in *)
(*             let%bind mono = State.map (inst poly) ~f:Result.return in *)
(*             match Lowercase.Map.find field_mono_map field with *)
(*             | None -> *)
(*                 State.Result.error *)
(*                   [%message "Unknown field" (field : Lowercase.t)] *)
(*             | Some field_mono -> unify field_mono mono) *)
(*       in *)
(*       poly_res *)

(* and poly_of_expr expr = *)
(*   let open State.Result.Let_syntax in *)
(*   match expr with *)
(*   | Ast.Node node -> poly_of_node node *)
(*   | If (pred, then_, else_) -> *)
(*       let%bind pred_mono = poly_of_expr pred >>= inst_result in *)
(*       let%bind then_mono = poly_of_expr then_ >>= inst_result in *)
(*       let%bind else_mono = poly_of_expr else_ >>= inst_result in *)
(*       let%bind () = unify pred_mono bool_type in *)
(*       let%map () = unify then_mono else_mono in *)
(*       then_mono *)

let rec mono_of_node node =
  let open State.Result.Let_syntax in
  match node with
  | Ast.Literal (Ast.Literal.Int _) -> State.Result.return int_type
  | Ast.Literal (Ast.Literal.Float _) -> State.Result.return float_type
  | Ast.Literal (Ast.Literal.Bool _) -> State.Result.return bool_type
  | Ast.Literal Ast.Literal.Unit -> State.Result.return unit_type
  | Ast.Literal (Ast.Literal.String _) -> State.Result.return string_type
  | Ast.Literal (Ast.Literal.Char _) -> State.Result.return char_type
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
  | Ast.Constructor constructor -> (
      let%bind arg, poly_res = lookup_constructor constructor in
      let%bind mono_res = inst_result poly_res in
      match arg with
      | None -> return mono_res
      | Some poly_arg ->
          let%map mono_arg = inst_result poly_arg in
          Lambda (mono_arg, mono_res))
  | Ast.Record qualified_record ->
      let qualifications, record = Qualified.split qualified_record in
      let%bind () = open_module qualifications in
      let%bind field_map, poly_res =
        lookup_record (Qualified.Unqualified record)
      in
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
            let%bind poly = poly_of_expr expr in
            let%bind mono = State.map (inst poly) ~f:Result.return in
            match Lowercase.Map.find field_mono_map field with
            | None ->
                State.Result.error
                  [%message "Unknown field" (field : Lowercase.t)]
            | Some field_mono -> unify field_mono mono)
      in
      poly_res

and mono_of_expr expr =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node node -> poly_of_node node
  | If (pred, then_, else_) ->
      let%bind pred_mono = poly_of_expr pred >>= inst_result in
      let%bind then_mono = poly_of_expr then_ >>= inst_result in
      let%bind else_mono = poly_of_expr else_ >>= inst_result in
      let%bind () = unify pred_mono bool_type in
      let%map () = unify then_mono else_mono in
      then_mono
