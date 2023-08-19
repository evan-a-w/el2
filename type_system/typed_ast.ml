open! Core
open! Shared
open! Frontend

module Literal = struct
  type t = Ast.Literal.t =
    | Unit
    | Int of int
    | Bool of bool
    | Float of float
    | String of string
    | Char of char
  [@@deriving sexp, equal, hash, compare]

  let type_proof_of_t x =
    match x with
    | Unit -> Ty.unit_type
    | Int _ -> Ty.int_type
    | Bool _ -> Ty.bool_type
    | Float _ -> Ty.float_type
    | String _ -> Ty.string_type
    | Char _ -> Ty.char_type
  ;;

  let mono_of_t x =
    let type_proof = type_proof_of_t x in
    Ty.Named type_proof
  ;;

  let poly_of_t x =
    let mono = mono_of_t x in
    Ty.Mono mono
  ;;
end

type node =
  | Var of Lowercase.t Qualified.t * Ty.binding_id
  | Literal of Literal.t
  | Tuple of expr list Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and binding =
  | Name_binding of Lowercase.t
  | Constructor_binding of Uppercase.t Qualified.t * binding option
  | Literal_binding of Literal.t
  | Record_binding of binding Lowercase.Map.t Qualified.t
  | Tuple_binding of binding list Qualified.t
  | Renamed_binding of binding * Lowercase.t
  | Reference_binding of binding
[@@deriving sexp, equal, hash, compare]

and let_each = binding * expr [@@deriving sexp, equal, hash, compare]

and let_def =
  | Rec of let_each list
  | Nonrec of let_each
[@@deriving sexp, equal, hash, compare]

and expr = expr_inner * Ty.mono [@@deriving sexp, equal, hash, compare]

and expr_inner =
  | Node of node
  | If of expr * expr * expr
  | Lambda of binding * expr
  | App of expr * expr
  | Let_in of let_def * expr
  | Ref of expr
  | Deref of expr
  | Field_access of expr * Lowercase.t Qualified.t
  | Field_set of (expr * Lowercase.t Qualified.t * expr)
  | Match of expr * (binding * expr) list
[@@deriving sexp, equal, hash, compare]

let expr_of_literal x = Node (Literal x), Literal.mono_of_t x

let map_binding_inner ~f = function
  | Name_binding x -> Name_binding x
  | Constructor_binding (x, y) -> Constructor_binding (x, Option.map ~f y)
  | Literal_binding x -> Literal_binding x
  | Record_binding x ->
    Record_binding (Qualified.map x ~f:(Lowercase.Map.map ~f))
  | Tuple_binding x -> Tuple_binding (Qualified.map x ~f:(List.map ~f))
  | Renamed_binding (x, y) -> Renamed_binding (f x, y)
  | Reference_binding x -> Reference_binding (f x)
;;

let map_binding_inner_m ~f =
  let open State.Result.Let_syntax in
  function
  | Name_binding x -> return @@ Name_binding x
  | Constructor_binding (x, y) ->
    let%map y =
      match y with
      | Some y ->
        let%map y = f y in
        Some y
      | None -> return None
    in
    Constructor_binding (x, y)
  | Literal_binding x -> return @@ Literal_binding x
  | Record_binding x ->
    let%map map =
      Qualified.map_m
        x
        ~f:
          (Map.fold ~init:(return Lowercase.Map.empty) ~f:(fun ~key ~data acc ->
             let%bind acc = acc in
             let%map data = f data in
             Map.add_exn acc ~key ~data))
    in
    Record_binding map
  | Tuple_binding x ->
    let%map list =
      Qualified.map_m x ~f:(fun l -> State.Result.all @@ List.map l ~f)
    in
    Tuple_binding list
  | Renamed_binding (x, y) ->
    let%map x = f x in
    Renamed_binding (x, y)
  | Reference_binding x ->
    let%map x = f x in
    Reference_binding x
;;

module Type_def = struct
  type t =
    { type_def : Ty.user_type
    ; type_binding : Ast.Type_binding.t
    ; type_proof : Ty.type_proof
    }
  [@@deriving sexp, equal, hash, compare]
end

type toplevel_type =
  | Sig_binding of binding * Ty.poly
  | Sig_module of module_description
  | Sig_type_def of Type_def.t
[@@deriving sexp, equal, hash, compare]

and module_sig = toplevel_type list [@@deriving sexp, equal, hash, compare]

and module_description =
  { module_name : Uppercase.t Qualified.t
  ; functor_args : (Uppercase.t * module_sig) list
  }
[@@deriving sexp, equal, hash, compare]

type toplevel =
  | Type_def of Type_def.t
  | Let of let_def
  | Module_def of module_def
[@@deriving sexp, equal, hash, compare]

and module_ = module_impl Ty.module_bindings
[@@deriving sexp, equal, hash, compare]

and module_def = module_description * module_
[@@deriving sexp, equal, hash, compare]

and module_impl =
  | Here of toplevel list
  | There of module_
[@@deriving sexp, equal, hash, compare]

let empty_data = Here []

(* TODO: pretty print typed ast*)
