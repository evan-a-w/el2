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
  [@@deriving sexp, equal, compare]

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
  | Var of
      Lowercase.t Qualified.t
      * Ty.binding_state ref
      * Ty.mono Lowercase.Map.t (* map for instantiated tyvars *)
  | Literal of Literal.t
  | Tuple of expr list Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, compare]

and binding_inner =
  | Name_binding of Ty.binding_state ref
  | Constructor_binding of Uppercase.t Qualified.t * binding option
  | Literal_binding of Literal.t
  | Record_binding of binding Lowercase.Map.t Qualified.t
  | Tuple_binding of binding list Qualified.t
  | Renamed_binding of binding * Lowercase.t * Ty.binding_state ref
  | Reference_binding of binding
[@@deriving sexp, equal, compare]

and binding = binding_inner * Ty.mono [@@deriving sexp, equal, compare]
and let_each = binding * expr [@@deriving sexp, equal, compare]

and let_def =
  | Rec of let_each list
  | Nonrec of let_each
[@@deriving sexp, equal, compare]

and expr = expr_inner * Ty.mono [@@deriving sexp, equal, compare]

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
[@@deriving sexp, equal, compare]

module Type_def = struct
  type t =
    { type_def : Ty.user_type
    ; type_binding : Ast.Type_binding.t
    ; type_proof : Ty.type_proof
    }
  [@@deriving sexp, equal, compare]
end

type toplevel_type =
  | Sig_binding of binding * Ty.poly
  | Sig_module of module_description
  | Sig_type_def of Type_def.t
[@@deriving sexp, equal, compare]

and module_sig = toplevel_type list [@@deriving sexp, equal, compare]

and module_description =
  { module_name : Uppercase.t Qualified.t
  ; functor_args : (Uppercase.t * module_sig) list
  }
[@@deriving sexp, equal, compare]

type toplevel =
  | Type_def of Type_def.t
  | Let of let_def
  | Module_def of module_def
[@@deriving sexp, equal, compare]

and module_ = module_impl Ty.module_bindings
[@@deriving sexp, equal, compare]

and module_def = module_description * module_
[@@deriving sexp, equal, compare]

and module_impl =
  | Here of toplevel list
  | There of module_
[@@deriving sexp, equal, compare]
