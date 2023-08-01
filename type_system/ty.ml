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

  let rec find_in_modules :
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
        >>= find_in_modules ~qualifications ~search_for

  let find_type_constructor module_ ~qualified_name =
    let qualifications, type_name = Qualified.split qualified_name in
    match
      find_in_modules module_ ~qualifications ~search_for:(fun module_ ->
          Lowercase.Map.find module_.type_constructors type_name)
    with
    | Some x -> State.Result.return x
    | None ->
        State.Result.error
          [%message
            "type constructor not found"
              (qualified_name : Lowercase.t Qualified.t)]

  let find_type module_ ~qualified_name =
    let qualifications, type_name = Qualified.split qualified_name in
    find_in_modules module_ ~qualifications ~search_for:(fun module_ ->
        match Lowercase.Map.find module_.type_constructors type_name with
        | None -> None
        | Some (None, mono) -> Some mono
        | Some _ -> None)

  let find_value module_ ~qualified_name =
    let qualifications, name = Qualified.split qualified_name in
    find_in_modules module_ ~qualifications ~search_for:(fun module_ ->
        Lowercase.Map.find module_.values name)

  let add_constructor module_ ~name ~type_constructor_arg ~mono =
    match
      Uppercase.Map.add module_.constructors ~key:name
        ~data:(type_constructor_arg, mono)
    with
    | `Ok constructors -> `Ok { module_ with constructors }
    | `Duplicate -> `Duplicate

  let add_record module_ ~field_map ~poly =
    let field_set =
      Lowercase.Map.fold field_map ~init:Lowercase.Set.empty
        ~f:(fun ~key ~data:_ acc -> Lowercase.Set.add acc key)
    in
    match
      Lowercase.Set.Map.add module_.records ~key:field_set
        ~data:(field_map, poly)
    with
    | `Ok records -> `Ok { module_ with records }
    | `Duplicate -> `Duplicate
end
