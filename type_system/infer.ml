open! Core
open! Shared
open! Frontend

type variance_map = Variance.t Lowercase.Map.t
[@@deriving sexp, equal, hash, compare]

type type_constructor_arg =
  | Tuple_arg of (Variance.t * Lowercase.t) list
  | Single_arg of Variance.t * Lowercase.t
[@@deriving sexp, equal, hash, compare]

let show_type_constructor_arg = function
  | Tuple_arg [ (_, s) ] | Single_arg (_, s) -> s
  | Tuple_arg l -> "(" ^ String.concat ~sep:", " (List.map l ~f:snd) ^ ")"

type type_constructor =
  type_constructor_arg option * mono
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
and type_proof = {
  type_name : Lowercase.t Qualified.t;
  ordering : Lowercase.t list option;
  tyvar_map : mono Lowercase.Map.t;
  level : int;
}
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

module Mono_ufds = Ufds.Make (struct
  type t = mono [@@deriving sexp, equal, hash, compare]
end)

module Module_path = Qualified.Make (struct
  type arg = Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

type level = int [@@deriving sexp, equal, hash, compare]

type module_bindings = {
  toplevel_vars : poly list Lowercase.Map.t;
  toplevel_records : (poly Lowercase.Map.t * poly) Lowercase.Set.Map.t;
  toplevel_constructors : (poly option * poly) Uppercase.Map.t;
  toplevel_type_constructors : type_constructor Lowercase.Map.t;
  toplevel_modules : module_bindings Uppercase.Map.t;
  opened_modules : module_bindings List.t;
}
[@@deriving sexp, equal, hash, compare, fields]

let make_abstract s =
  Abstract
    {
      type_name = Qualified.Unqualified s;
      level = 0;
      ordering = None;
      tyvar_map = Lowercase.Map.empty;
    }

let int_type = make_abstract "int"
let float_type = make_abstract "float"
let bool_type = make_abstract "bool"
let unit_type = make_abstract "unit"
let string_type = make_abstract "string"
let char_type = make_abstract "char"

let base_module_bindings =
  {
    toplevel_vars =
      (let init = Lowercase.Map.empty in
       Lowercase.Map.add_multi init ~key:"&"
         ~data:(Forall ("a", Mono (Lambda (TyVar "a", Pointer (TyVar "a"))))));
    toplevel_records = Lowercase.Set.Map.empty;
    toplevel_constructors = Uppercase.Map.empty;
    toplevel_type_constructors =
      Lowercase.Map.of_alist_exn
        [
          ("int", (None, int_type));
          ("float", (None, float_type));
          ("bool", (None, bool_type));
          ("unit", (None, unit_type));
          ("string", (None, string_type));
          ("char", (None, char_type));
        ];
    toplevel_modules = Uppercase.Map.empty;
    opened_modules = [];
  }

let empty_module_bindings =
  {
    toplevel_vars = Lowercase.Map.empty;
    toplevel_records = Lowercase.Set.Map.empty;
    toplevel_constructors = Uppercase.Map.empty;
    toplevel_type_constructors = Lowercase.Map.empty;
    toplevel_modules = Uppercase.Map.empty;
    opened_modules = [ base_module_bindings ];
  }

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

let operate_on_toplevel_type_constructors arg name mono ~f =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let data = (arg, mono) in
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
    current_module_binding = empty_module_bindings;
    module_history = { current_name = "Base"; previous_modules = [] };
    symbol_n = 0;
    (* type_vars = Lowercase.Map.empty; *)
    (* current_level = 0; *)
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

let add_type name mono = add_type_constructor None name mono

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

let lookup_type ?(type_var = true) qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let type_var_fn = if type_var then Option.some else Fn.const None in
  let type_var_type =
    match qualifications with [] -> type_var_fn (TyVar type_name) | _ -> None
  in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        match
          Lowercase.Map.find module_bindings.toplevel_type_constructors
            type_name
        with
        | None -> None
        | Some (None, mono) -> Some mono
        | Some _ -> None)
  in
  match Option.first_some res type_var_type with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

let get_type_proof mono =
  match mono with
  | Recursive_constructor proof
  | Abstract proof
  | Record (proof, _)
  | Enum (proof, _) ->
      Some proof
  | _ -> None

let get_ordering type_name =
  let open State.Result.Let_syntax in
  let%map _, t = lookup_type_constructor type_name in
  let ordering =
    match get_type_proof t with
    | Some { ordering; _ } -> ordering
    | None -> None
  in
  Option.value ~default:[] ordering

let rec show_type_proof { type_name; ordering = _; tyvar_map; _ } =
  let open State.Result.Let_syntax in
  let%bind ordering = get_ordering type_name in
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
  let type_string = Qualified.show Fn.id type_name in
  prefix_string ^ type_string

and show_mono mono =
  let open State.Result.Let_syntax in
  match mono with
  | Weak s | TyVar s -> return s
  | Recursive_constructor proof
  | Abstract proof
  | Record (proof, _)
  | Enum (proof, _) ->
      show_type_proof proof
  | Lambda (a, b) ->
      let%bind a = show_mono a in
      let%map b = show_mono b in
      a ^ " -> " ^ b
  | Tuple l ->
      let%map shown = List.map ~f:show_mono l |> State.Result.all in
      "(" ^ String.concat ~sep:", " shown ^ ")"
  | Pointer m ->
      let%map m = show_mono m in
      "&" ^ m

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

and map_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  {
    type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_ty_vars ~f);
  }

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
  | Record (type_proof, l) ->
      let%bind type_proof = map_type_proof_m ~f type_proof in
      let%map l =
        State.Result.all
          (List.map l ~f:(fun (x, (y, mut)) ->
               let%map y = map_ty_vars_m ~f y in
               (x, (y, mut))))
      in
      Record (type_proof, l)
  | Enum (type_proof, l) ->
      let%bind type_proof = map_type_proof_m ~f type_proof in
      let%map l =
        State.Result.all
          (List.map l ~f:(fun (x, y) ->
               let%map y =
                 match y with
                 | Some x -> map_ty_vars_m ~f x >>| Option.some
                 | None -> return None
               in
               (x, y)))
      in
      Enum (type_proof, l)
  | Pointer x ->
      let%map x = map_ty_vars_m ~f x in
      Pointer x
  | Recursive_constructor type_proof ->
      let%map type_proof = map_type_proof_m ~f type_proof in
      Recursive_constructor type_proof
  | Abstract type_proof ->
      let%map type_proof = map_type_proof_m ~f type_proof in
      Abstract type_proof

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

let rec map_weak_vars ~f (mono : mono) =
  match mono with
  | Weak m -> Option.value (f m) ~default:mono
  | TyVar _ -> mono
  | Lambda (a, b) -> Lambda (map_weak_vars ~f a, map_weak_vars ~f b)
  | Tuple l -> Tuple (List.map l ~f:(map_weak_vars ~f))
  | Record (type_proof, l) ->
      Record
        ( map_weak_type_proof ~f type_proof,
          List.Assoc.map l ~f:(Tuple2.map_fst ~f:(map_weak_vars ~f)) )
  | Enum (type_proof, l) ->
      let l = List.Assoc.map l ~f:(Option.map ~f:(map_weak_vars ~f)) in
      Enum (map_weak_type_proof ~f type_proof, l)
  | Pointer x -> Pointer (map_weak_vars ~f x)
  | Recursive_constructor type_proof ->
      Recursive_constructor (map_weak_type_proof ~f type_proof)
  | Abstract type_proof -> Abstract (map_weak_type_proof ~f type_proof)

and map_weak_type_proof ~f ({ tyvar_map; _ } as type_proof) =
  {
    type_proof with
    tyvar_map = Lowercase.Map.map tyvar_map ~f:(map_weak_vars ~f);
  }

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

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> snd @@ List.unzip l
  | Single_arg (_, x) -> [ x ]

let free_ty_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_ty_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x);
  !set

let free_weak_vars mono =
  let set = ref Lowercase.Set.empty in
  iter_weak_vars mono ~f:(fun x -> set := Lowercase.Set.add !set x);
  !set

let replace_ty_vars ~replacement_map =
  map_ty_vars ~f:(Lowercase.Map.find replacement_map)

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
      Pointer mono
  | Ast.Type_expr.Tuple l ->
      let%map monos = State.Result.all (List.map l ~f:type_of_type_expr) in
      Tuple monos
  | Arrow (first, second) ->
      let%map first = type_of_type_expr first
      and second = type_of_type_expr second in
      Lambda (first, second)
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (first, second) ->
      let%bind constructor_arg, mono = lookup_type_constructor second in
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
      replace_ty_vars ~replacement_map mono

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

let type_proof_of_monos ~type_name monos level =
  let free_var_set =
    List.fold monos ~init:Lowercase.Set.empty ~f:(fun acc mono ->
        Lowercase.Set.union acc (free_ty_vars mono))
  in
  let tyvar_map =
    Lowercase.Set.fold free_var_set ~init:Lowercase.Map.empty ~f:(fun acc x ->
        Lowercase.Map.add_exn acc ~key:x ~data:(TyVar x))
  in
  { type_name; tyvar_map; ordering = None; level }

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

let set_ordering (mono : mono) ~ordering =
  match mono with
  | Recursive_constructor p ->
      Recursive_constructor { p with ordering = Some ordering }
  | Abstract p -> Abstract { p with ordering = Some ordering }
  | Record (p, x) -> Record ({ p with ordering = Some ordering }, x)
  | Enum (p, x) -> Enum ({ p with ordering = Some ordering }, x)
  | _ -> mono

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
        | Ast.Type_binding.Single (v, l) -> Some (Single_arg (v, l))
        | Ast.Type_binding.Tuple l -> Some (Tuple_arg l)
      in
      let ordering =
        Option.map constructor_arg ~f:constructor_arg_free_ty_vars
        |> Option.value ~default:[]
      in
      let lhs_ty_vars =
        List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc key ->
            Lowercase.Map.add_exn acc ~key ~data:(TyVar key))
      in
      let recursive_constructor =
        Recursive_constructor
          {
            type_name = Qualified.Unqualified type_name;
            ordering = Some ordering;
            level = 0;
            tyvar_map = lhs_ty_vars;
          }
      in
      let%bind () =
        add_type_constructor constructor_arg type_name recursive_constructor
      in
      let%bind mono =
        type_of_type_def_lit ~type_name:(Qualified.Unqualified type_name)
          ~update_records_and_constructors:true type_def
      in
      let mono = set_ordering mono ~ordering in
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
  let%bind arg, poly_res = lookup_constructor constructor in
  match arg with
  | None ->
      let%map res = inst_result poly_res in
      (None, res)
  | Some poly_arg ->
      let%map mono_arg, mono_res =
        match%bind.State inst_many [ poly_arg; poly_res ] with
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

let unfold_once { type_name = name; tyvar_map = replacement_map; _ } mono =
  let open State.Result.Let_syntax in
  let%bind _, type_ = lookup_type_constructor name in
  let%map poly = State.map (gen type_) ~f:Result.return in
  let _, mono' = split_poly poly in
  let mono' = replace_ty_vars ~replacement_map mono' in
  (mono', mono)

let rec get_to_same_recursion_level ~unification_error mono1 mono2 =
  let open State.Result.Let_syntax in
  match (get_type_proof mono1, get_type_proof mono2) with
  | None, _ | _, None -> return (mono1, mono2)
  | Some p1, Some p2 -> (
      let level1 = p1.level in
      let level2 = p2.level in
      match Int.compare level1 level2 with
      | 0 -> return (mono1, mono2)
      | x when x < 0 ->
          let%bind mono1, mono2 = unfold_once p1 mono2 in
          get_to_same_recursion_level ~unification_error mono1 mono2
      | _ ->
          let%bind mono2, mono1 = unfold_once p2 mono1 in
          get_to_same_recursion_level ~unification_error mono1 mono2)

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
  match (mono1, mono2) with
  | ( (Recursive_constructor p1 | Abstract p1 | Record (p1, _) | Enum (p1, _)),
      (Recursive_constructor p2 | Abstract p2 | Record (p2, _) | Enum (p2, _)) )
    ->
      unify_type_proof ~unification_error p1 p2
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
  | Tuple l1, Tuple l2 -> unify_lists ~unification_error l1 l2
  | _ -> unification_error ()

and unify_type_proof ~unification_error
    ({ type_name = name1; tyvar_map = rep1; _ } as a)
    ({ type_name = name2; tyvar_map = rep2; _ } as b) =
  let monos1 = Lowercase.Map.data rep1 in
  let%bind.State monos1 = State.all (List.map ~f:find monos1) in
  let monos2 = Lowercase.Map.data rep2 in
  let%bind.State monos2 = State.all (List.map ~f:find monos2) in
  match Qualified.equal Lowercase.equal name1 name2 with
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
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  let unification_error () = unification_error mono1 mono2 in
  match (mono1, mono2) with
  | ( (Recursive_constructor p1 | Abstract p1 | Record (p1, _) | Enum (p1, _)),
      (Recursive_constructor p2 | Abstract p2 | Record (p2, _) | Enum (p2, _)) )
    ->
      unify_less_general_type_proof ~unification_error p1 p2
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
  | Pointer x, Pointer y -> unify_less_general x y
  | Lambda (x1, x2), Lambda (y1, y2) ->
      let%bind () = unify_less_general x1 y1 in
      unify_less_general x2 y2
  | Tuple l1, Tuple l2 -> unify_less_general_lists ~unification_error l1 l2
  | _ -> unification_error ()

and unify_less_general_type_proof ~unification_error
    ({ type_name = name1; tyvar_map = rep1; _ } as a)
    ({ type_name = name2; tyvar_map = rep2; _ } as b) =
  let monos1 = Lowercase.Map.data rep1 in
  let%bind.State monos1 = State.all (List.map ~f:find monos1) in
  let monos2 = Lowercase.Map.data rep2 in
  let%bind.State monos2 = State.all (List.map ~f:find monos2) in
  match Qualified.equal Lowercase.equal name1 name2 with
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
  | Ast.Literal.Int _ -> State.Result.return int_type
  | Ast.Literal.Float _ -> State.Result.return float_type
  | Ast.Literal.Bool _ -> State.Result.return bool_type
  | Ast.Literal.Unit -> State.Result.return unit_type
  | Ast.Literal.String _ -> State.Result.return string_type
  | Ast.Literal.Char _ -> State.Result.return char_type

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
      (Pointer mono, vars)
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
      let%bind field_map, poly = lookup_record qualified_map in
      let%bind mono_searched = inst_result poly in
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
      let%bind field_map, poly_res =
        lookup_record (Qualified.Unqualified record)
      in
      let%bind mono_res = inst_result poly_res in
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
      let%bind () = unify (Pointer ty_var) mono in
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
      let%bind field_map, poly = lookup_record qualified_map in
      let%bind mono_searched = inst_result poly in
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

and mono_of_expr expr =
  let open State.Result.Let_syntax in
  match expr with
  | Ast.Node node -> mono_of_node node
  | If (pred, then_, else_) ->
      let%bind pred_mono = mono_of_expr pred in
      let%bind then_mono = mono_of_expr then_ in
      let%bind else_mono = mono_of_expr else_ in
      let%bind () = unify pred_mono bool_type in
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
    | Ast.Rec l ->
        let%map _ = add_rec_bindings l in
        ()
    | Ast.Nonrec (binding, expr) ->
        let%map _ = add_nonrec_bindings ~binding ~expr in
        ()
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
  let%bind () =
    Lowercase.Map.fold joined_type_constructors ~init:(return ())
      ~f:(fun ~key:_ ~data:(left, right) acc ->
        let%bind () = acc in
        let arg1, mono1 = left in
        let arg2, mono2 = right in
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
        unify mono1 mono2)
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
  return signature

let rec process_module_named (f : Uppercase.t Qualified.t) =
  let _ = f in
  failwith "TODO"

and process_struct (_ : Ast.toplevel list) = failwith "TODO"

and process_functor_app (f : Uppercase.t Qualified.t) (a : Ast.module_def list)
    =
  let _ = (f, a) in
  failwith "TODO"

and process_sig (_ : Ast.module_sig) = failwith "TODO"

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
      let%bind _ = unify_module_bindings ~signature ~definition in
      change_to_module name definition

let rec process_module
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
  | Record (type_proof, l) ->
      Record
        ( replace_type_name_proof ~type_name type_proof,
          List.Assoc.map l ~f:(Tuple2.map_fst ~f:(replace_type_name ~type_name))
        )
  | Enum (type_proof, l) ->
      let l =
        List.Assoc.map l ~f:(Option.map ~f:(replace_type_name ~type_name))
      in
      Enum (replace_type_name_proof ~type_name type_proof, l)
  | Pointer x -> Pointer (replace_type_name ~type_name x)
  | Recursive_constructor type_proof ->
      Recursive_constructor (replace_type_name_proof ~type_name type_proof)
  | Abstract type_proof ->
      Abstract (replace_type_name_proof ~type_name type_proof)

and replace_type_name_proof ~type_name type_proof =
  { type_proof with type_name = Qualified.Unqualified type_name }

let rec show_mono_def (mono : mono) =
  let open State.Result.Let_syntax in
  match mono with
  | Recursive_constructor { type_name; _ } ->
      let%bind mono = lookup_type ~type_var:false type_name in
      show_mono_def mono
  | Abstract { type_name; _ } ->
      let name = Qualified.show Fn.id type_name in
      return name
  | Weak s -> return [%string "weak %{s}"]
  | TyVar s -> return s
  | Lambda _ | Tuple _ | Pointer _ -> show_mono mono
  | Record (_, fields) ->
      [%sexp
        (fields : (Lowercase.t * (mono * [ `Mutable | `Immutable ])) List.t)]
      |> Sexp.to_string_hum |> return
  | Enum (_, cons) ->
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
      "\n" ^ String.concat ~sep:"\n" l

let show_module_bindings
    {
      toplevel_vars;
      toplevel_records = _;
      toplevel_type_constructors;
      toplevel_modules = _;
      _;
    } =
  let open State.Result.Let_syntax in
  let%bind type_strings =
    Lowercase.Map.to_alist toplevel_type_constructors
    |> List.map ~f:(fun (type_name, (args, mono)) ->
           let prefix_str =
             match args with
             | Some args -> show_type_constructor_arg args ^ " "
             | None -> ""
           in
           let%map rhs =
             match mono with
             | Abstract { type_name = type_name'; _ }
               when Qualified.equal String.equal
                      (Qualified.Unqualified type_name) type_name' ->
                 return None
             | _ -> show_mono_def mono >>| Option.some
           in
           match rhs with
           | Some mono_s ->
               [%string "type %{prefix_str}%{type_name} = %{mono_s}"]
           | None -> [%string "type %{prefix_str}%{type_name}"])
    |> State.Result.all
  in
  let%map var_strings =
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
  List.concat [ type_strings; var_strings ] |> String.concat ~sep:"\n\n"
