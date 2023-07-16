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

type type_id = int [@@deriving sexp, equal, hash, compare]

(* TODO: once mutability is added, make mutable type stuff that aren't generalized in let expressions

   should i use mutable fields or have types be mutable/immutable instances??
*)
type mono_inner =
  | Abstract of type_id
  | Weak of Lowercase.t
  | TyVar of Lowercase.t
  (* | Concrete of string Qualified.t *)
  | Concrete of type_id
  | Lambda of mono * mono
  | Tuple of mono list
  | Type_function of mono * mono
  | Record of mono
  | Pointer of mono
[@@deriving sexp, equal, hash, compare]

(* always safe to generalize variables that are only covariant *)
and mono = mono_inner * Variance.t Lowercase.Map.t
[@@deriving sexp, equal, hash, compare]

and poly = Mono of mono | Forall of Lowercase.t * poly
[@@deriving sexp, equal, hash, compare]

and var_map = (mono * Lowercase.Set.t) Lowercase.Map.t
and type_map = (mono * type_id) Lowercase.Map.t

module Mono_ufds = Ufds.Make (struct
  type t = mono [@@deriving sexp, equal, hash, compare]
end)

module Module_path = Qualified.Make (struct
  type arg = Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

type module_bindings = {
  toplevel_vars : var_map;
  toplevel_records : (Lowercase.Set.t * mono) list;
  toplevel_types : type_map;
  toplevel_modules : module_bindings Uppercase.Map.t;
  opened_modules : module_bindings List.t;
}
[@@deriving sexp, equal, hash, compare]

type state = {
  mono_ufds : Mono_ufds.t;
  substs : mono Lowercase.Map.t;
  vars : var_map;
  current_module_binding : module_bindings;
  current_qualification : Uppercase.t list;
}
[@@deriving sexp, equal, compare]

type 'a state_m = ('a, state) State.t [@@deriving sexp]
type 'a state_result_m = ('a, Sexp.t, state) State.Result.t [@@deriving sexp]

let rec search_modules module_bindings ~qualifications
    ~(search_for : module_bindings -> 'a option) : 'a option =
  match Sequence.next qualifications with
  | None -> Some module_bindings
  | Some (name, qualifications) -> (
      let open Option.Let_syntax in
      let first =
        Uppercase.Map.find module_bindings.toplevel_modules name
        >>= search_modules ~qualifications ~search_for
        >>= search_for
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

let merge_variances_maps variances1 variances2 =
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
      let%map ((_, variance_map) as mono) =
        process_type_def_lit_type_expr type_expr
      in
      (Pointer mono, variance_map)
  | Ast.Type_expr.Single _ | Ast.Type_expr.Tuple _ | Ast.Type_expr.Multi (_, _)
    ->
      failwith "TODO"

let process_type_def (_type_binding : Ast.Type_def_lit.t Ast.type_description) =
  failwith "TODO"
(* let process_type_def (type_def : Ast.Type_def_lit.t Ast.type_description) = *)
(*   failwith "TODO" *)

let find mono =
  let%bind.State state = State.get in
  let mono, mono_ufds = Mono_ufds.find state.mono_ufds mono in
  let%map.State () = State.put { state with mono_ufds } in
  mono

let union mono1 mono2 =
  let%bind.State state = State.get in
  let mono_ufds = Mono_ufds.union state.mono_ufds mono1 mono2 in
  State.put { state with mono_ufds }

let add_constraint ~var ~ty =
  let%bind.State state = State.get in
  State.put { state with substs = Map.set state.substs ~key:var ~data:ty }

let unify mono1 mono2 =
  (* let open State.Result in *)
  let%bind.State mono1 = find mono1 in
  let%bind.State mono2 = find mono2 in
  match (mono1, mono2) with _ -> failwith "TODO"
