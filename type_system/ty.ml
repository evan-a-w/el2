open! Core
open! Shared

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

let get_type_proof mono =
  match mono with
  | Recursive_constructor proof
  | Abstract proof
  | Record (proof, _)
  | Enum (proof, _) ->
      Some proof
  | _ -> None

type poly = Mono of mono | Forall of Lowercase.t * poly
[@@deriving sexp, equal, hash, compare, variants]

module Module_path = Qualified.Make (struct
  type arg = Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

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

module Module = struct
  type module_ = {
    values : poly list Lowercase.Map.t;
    records : (poly Lowercase.Map.t * poly) Lowercase.Set.Map.t;
    constructors : (poly option * poly) Uppercase.Map.t;
    type_constructors : type_constructor Lowercase.Map.t;
    modules : module_ Uppercase.Map.t;
  }
  [@@deriving sexp, equal, hash, compare, fields]

  type in_scope = { module_ : module_; opened_modules : module_ list }
  [@@deriving sexp, equal, hash, compare, fields]

  let base_module =
    {
      values =
        (let init = Lowercase.Map.empty in
         Lowercase.Map.add_multi init ~key:"&"
           ~data:(Forall ("a", Mono (Lambda (TyVar "a", Pointer (TyVar "a"))))));
      records = Lowercase.Set.Map.empty;
      constructors = Uppercase.Map.empty;
      type_constructors =
        Lowercase.Map.of_alist_exn
          [
            ("int", (None, int_type));
            ("float", (None, float_type));
            ("bool", (None, bool_type));
            ("unit", (None, unit_type));
            ("string", (None, string_type));
            ("char", (None, char_type));
          ];
      modules = Uppercase.Map.empty;
    }

  let empty_module =
    {
      values = Lowercase.Map.empty;
      records = Lowercase.Set.Map.empty;
      constructors = Uppercase.Map.empty;
      type_constructors = Lowercase.Map.empty;
      modules = Uppercase.Map.empty;
    }

  let empty_in_scope =
    { module_ = empty_module; opened_modules = [ base_module ] }

  let add_module module_ ~name ~value =
    {
      module_ with
      modules = Uppercase.Map.set module_.modules ~key:name ~data:value;
    }

  let map_type_constructors module_ ~f =
    let%map.State.Result type_constructors = f module_.type_constructors in
    { module_ with type_constructors }

  let add_value module_ ~name ~poly =
    let values = Lowercase.Map.add_multi module_.values ~key:name ~data:poly in
    { module_ with values }

  let pop_value module_ ~name =
    let values = Lowercase.Map.remove_multi module_.values name in
    { module_ with values }

  let rec lookup_in_module :
      type a.
      module_ ->
      qualifications:Qualified.qualifications ->
      search_for:(module_ -> a option) ->
      a option =
   fun module_ ~qualifications ~(search_for : module_ -> a option) ->
    match qualifications with
    | [] -> search_for module_
    | name :: qualifications ->
        let open Option.Let_syntax in
        Uppercase.Map.find module_.modules name
        >>= lookup_in_module ~qualifications ~search_for

  let lookup_in_scope { module_; opened_modules } ~qualifications ~search_for =
    let f = lookup_in_module ~qualifications ~search_for in
    match f module_ with
    | Some x -> Some x
    | None -> List.find_map opened_modules ~f

  let lookup_module in_scope ~qualifications =
    match
      lookup_in_scope in_scope ~qualifications ~search_for:Option.return
    with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message
            "module not found" (qualifications : Qualified.qualifications)]

  let lookup_type_constructor in_scope ~qualified_name =
    let qualifications, type_name = Qualified.split qualified_name in
    match
      lookup_in_scope in_scope ~qualifications ~search_for:(fun module_ ->
          Lowercase.Map.find module_.type_constructors type_name)
    with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message
            "type constructor not found"
              (qualified_name : Lowercase.t Qualified.t)]

  let lookup_type in_scope ~qualified_name =
    let qualifications, type_name = Qualified.split qualified_name in
    match
      lookup_in_scope in_scope ~qualifications ~search_for:(fun module_ ->
          match Lowercase.Map.find module_.type_constructors type_name with
          | None -> None
          | Some (None, mono) -> Some mono
          | Some _ -> None)
    with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

  let add_type_constructor module_ ~name ~arg ~mono =
    let f type_constructors =
      match Lowercase.Map.add type_constructors ~key:name ~data:(arg, mono) with
      | `Ok m -> State.Result.return m
      | `Duplicate ->
          State.Result.error
            [%message "Duplicate type constructor" (name : Lowercase.t)]
    in
    map_type_constructors module_ ~f

  let set_type_constructor module_ ~name ~arg ~mono =
    let f type_constructors =
      State.Result.return
      @@ Lowercase.Map.set type_constructors ~key:name ~data:(arg, mono)
    in
    map_type_constructors module_ ~f

  let add_type = add_type_constructor ~arg:None

  let lookup_value ~in_scope qualified_name =
    let qualifications, name = Qualified.split qualified_name in
    match
      lookup_in_scope in_scope ~qualifications ~search_for:(fun module_ ->
          Lowercase.Map.find module_.values name)
    with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message
            "value not found" (qualified_name : Lowercase.t Qualified.t)]

  let add_constructor module_ ~name ~arg_poly_option ~poly =
    match
      Uppercase.Map.add module_.constructors ~key:name
        ~data:(arg_poly_option, poly)
    with
    | `Ok constructors -> State.Result.return { module_ with constructors }
    | `Duplicate ->
        State.Result.error
          [%message "duplicate constructor" (name : Uppercase.t)]

  let add_record module_ ~field_map ~poly =
    let field_set =
      Lowercase.Map.fold field_map ~init:Lowercase.Set.empty
        ~f:(fun ~key ~data:_ acc -> Lowercase.Set.add acc key)
    in
    match
      Lowercase.Set.Map.add module_.records ~key:field_set
        ~data:(field_map, poly)
    with
    | `Ok records -> State.Result.return { module_ with records }
    | `Duplicate ->
        State.Result.error
          [%message "duplicate record" (field_set : Lowercase.Set.t)]

  let lookup_record in_scope ~qualified_map =
    let qualifications, map = Qualified.split qualified_map in
    let fields =
      Lowercase.Map.fold map ~init:Lowercase.Set.empty
        ~f:(fun ~key ~data:_ acc -> Lowercase.Set.add acc key)
    in
    let res =
      lookup_in_scope in_scope ~qualifications ~search_for:(fun module_ ->
          Lowercase.Set.Map.find module_.records fields)
    in
    match res with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message "record not in scope" (fields : Lowercase.Set.t)]

  let lookup_constructor in_scope ~qualified_constructor =
    let qualifications, name = Qualified.split qualified_constructor in
    let res =
      lookup_in_scope in_scope ~qualifications ~search_for:(fun module_ ->
          Uppercase.Map.find module_.constructors name)
    in
    match res with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message "constructor not in scope" (name : Uppercase.t)]

  let get_ordering in_scope ~type_name =
    let open State.Result.Let_syntax in
    let%map _, t = lookup_type_constructor in_scope ~qualified_name:type_name in
    let ordering =
      match get_type_proof t with
      | Some { ordering; _ } -> ordering
      | None -> None
    in
    Option.value ~default:[] ordering

  let rec show_type_proof in_scope
      ~type_proof:{ type_name; ordering = _; tyvar_map; _ } =
    let open State.Result.Let_syntax in
    let%bind ordering = get_ordering in_scope ~type_name in
    let%map type_var_map =
      List.map
        ~f:(fun k ->
          match Lowercase.Map.find tyvar_map k with
          | Some mono -> show_mono in_scope ~mono
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

  and show_mono in_scope ~mono =
    let open State.Result.Let_syntax in
    match mono with
    | Weak s | TyVar s -> return s
    | Recursive_constructor type_proof
    | Abstract type_proof
    | Record (type_proof, _)
    | Enum (type_proof, _) ->
        show_type_proof in_scope ~type_proof
    | Lambda (a, b) ->
        let%bind a = show_mono in_scope ~mono:a in
        let%map b = show_mono in_scope ~mono:b in
        a ^ " -> " ^ b
    | Tuple l ->
        let%map shown =
          List.map ~f:(fun mono -> show_mono in_scope ~mono) l
          |> State.Result.all
        in
        "(" ^ String.concat ~sep:", " shown ^ ")"
    | Pointer mono ->
        let%map m = show_mono in_scope ~mono in
        "&" ^ m

  let open_module ({ module_ = _; opened_modules } as in_scope)
      ~(qualifications : Qualified.qualifications) =
    let%map.State.Result module_ = lookup_module in_scope ~qualifications in
    let in_scope =
      { in_scope with opened_modules = module_ :: opened_modules }
    in
    in_scope

  let pop_module ({ module_ = _; opened_modules } as in_scope) =
    {
      in_scope with
      opened_modules = List.tl opened_modules |> Option.value ~default:[];
    }
end
