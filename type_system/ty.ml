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
