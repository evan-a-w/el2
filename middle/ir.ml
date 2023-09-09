open! Core
open! Shared
open! Type_system
module Module_path = Ty.Module_path

(* Typed_ast.expr but with
   1. Exhaustiveness checking on match statements (TODO)
   2. Breaking match statements into if statements and switches (same as c switches) (TODO)
   3. Unpacking pattern matching into multiple bindings, where each is
   just a Lowercase.t (TODO) *)

type binding_loc =
  { namespace : Module_path.t (* approx what file/module its in *)
  ; name : Lowercase.t
  }

type node =
  | Var of
      Lowercase.t (* name that maps directly to the binding *)
      * Ty.binding_id
      * Ty.mono Lowercase.Map.t (* map for instantiated tyvars *)
  | Literal of Typed_ast.Literal.t
  | Tuple of expr list Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and binding = Lowercase.t * Ty.binding_id * Ty.mono
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
  | Numbered_field_access of expr * int * Ty.mono
  | Union_check of expr * Uppercase.t * Ty.enum_type
  (* translates to if later down the line *)
  | Union_access of expr * Uppercase.t * Ty.enum_type
  | Field_access of expr * Lowercase.t * Ty.record_type
  | Field_set of (expr * Lowercase.t * Ty.record_type * expr)
[@@deriving sexp, equal, hash, compare]
