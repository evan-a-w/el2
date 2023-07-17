open! Core
open! Shared
open! Frontend

module Symbol_generator = struct
  type t = { mutable n : int; mutable printed : int } [@@deriving sexp]

  let create () = { n = 0; printed = 0 }

  let gensym t =
    let s = t.n in
    t.n <- s + 1;
    let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
    let s = String.make 1 letter ^ Int.to_string (s / 26) in
    s
end

type variance_map = Variance.t Lowercase.Map.t
[@@deriving sexp, equal, hash, compare]

type type_function_arg =
  | Tuple_arg of type_function_arg list
  | Single_arg of Variance.t * Lowercase.t
[@@deriving sexp, equal, hash, compare]

(* always safe to generalize variables that are only covariant *)
(* implicit variance for all but Type_function, Type_application and Record *)
type mono_inner =
  | Abstract
  | TyVar of Lowercase.t
  | Lambda of mono * mono
  | Tuple of mono list
  | Type_function of type_function_arg * mono
  | Type_application of mono * mono * variance_map
  | Record of mono * variance_map
  | Pointer of mono
[@@deriving sexp, equal, hash, compare]

and mono = mono_inner * Variance.t Lowercase.Map.t
[@@deriving sexp, equal, hash, compare]

and poly = Mono of mono | Forall of Lowercase.t * poly
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
  toplevel_types : mono Lowercase.Map.t;
  toplevel_modules : module_bindings Uppercase.Map.t;
  opened_modules : module_bindings List.t;
}
[@@deriving sexp, equal, hash, compare, fields]

let empty_module_bindngs =
  {
    toplevel_vars = Lowercase.Map.empty;
    toplevel_records = [];
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

let empty_state =
  {
    mono_ufds = Mono_ufds.empty;
    current_module_binding = empty_module_bindngs;
    current_qualification = [];
    type_var_map = Lowercase.Map.empty;
    symbol_n = 0;
  }

let gensym =
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
  State.put { state with current_module_binding }

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

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

let lookup_type qualified_name =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let type_var_type =
    match qualifications with
    | [] ->
        Option.bind (Lowercase.Map.find state.type_var_map type_name) ~f:List.hd
        |> Option.map ~f:(fun x -> TyVar x)
    | _ -> None
  in
  let res =
    search_modules state.current_module_binding ~qualifications
      ~search_for:(fun module_bindings ->
        Lowercase.Map.find module_bindings.toplevel_types type_name)
  in
  match Option.first_some type_var_type res with
  | Some x -> State.Result.return x
  | None ->
      State.Result.error
        [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]

let merge_variance_maps (variances1 : Variance.t Lowercase.Map.t) variances2 =
  Lowercase.Map.merge variances1 variances2 ~f:(fun ~key:_ -> function
    | `Left x | `Right x -> Some x | `Both (x, y) -> Some (Variance.merge x y))

let rec process_type_def_lit (type_def_lit : Ast.Type_def_lit.t) =
  match type_def_lit with
  | Ast.Type_def_lit.Record _ | Ast.Type_def_lit.Enum _
  | Ast.Type_def_lit.Type_expr _ ->
      failwith "TODO"

and process_type_def_lit_type_expr type_expr : mono state_result_m =
  let open State.Result.Let_syntax in
  match type_expr with
  | Ast.Type_expr.Pointer type_expr ->
      let%map mono = process_type_def_lit_type_expr type_expr in
      Pointer mono
  | Ast.Type_expr.Tuple l ->
      let%map monos =
        State.Result.all (List.map l ~f:process_type_def_lit_type_expr)
      in
      let variance_map =
        List.fold ~init:Lowercase.Map.empty ~f:merge_variance_maps variances
      in
      (Tuple monos, variance_map)
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (_, _) -> failwith "TODO"

let process_type_def (_type_binding : Ast.Type_def_lit.t Ast.type_description) =
  failwith "TODO"
(* let process_type_def (type_def : Ast.Type_def_lit.t Ast.type_description) = *)
(*   failwith "TODO" *)

let unify mono1 mono2 =
  (* let open State.Result in *)
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  match (mono1, mono2) with _ -> failwith "TODO"
