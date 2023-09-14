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
;;

module Binding_id = Id.Make ()

type type_constructor =
  type_constructor_arg option * user_type * type_proof
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
and type_proof =
  { type_name : Lowercase.t
  ; absolute_type_name : Lowercase.t Qualified.t
  ; ordering : Lowercase.t list option
  ; tyvar_map : mono Lowercase.Map.t
  ; type_id : type_id
  ; mem_rep : Mem_rep.abstract
  ; user_type : user_type
  }
[@@deriving sexp, equal, hash, compare]

and type_id = int [@@deriving sexp, equal, hash, compare]
and binding_id = Binding_id.t [@@deriving sexp, equal, hash, compare]

and mono =
  (* name and type args *)
  | Weak of Lowercase.t
  (* keep track of the path and arg for equality *)
  | TyVar of Lowercase.t
  | Function of mono * mono
  (* closures unify with all closures that have an equivalent mem rep and input/return type *)
  | Closure of mono * mono * closure_info
  | Tuple of mono list
  | Reference of mono
  | Named of type_proof
[@@deriving sexp, equal, hash, compare]

and closure_info =
  { closure_mem_rep : Mem_rep.abstract
  ; closed_args : (Binding_id.t * mono) list
  ; closed_vars : (Binding_id.t * mono) list
  }
[@@deriving sexp, equal, hash, compare]

and record_type = (Lowercase.t * (mono * [ `Mutable | `Immutable ])) list
[@@deriving sexp, equal, hash, compare]

and enum_type = (Uppercase.t * mono option) list
[@@deriving sexp, equal, hash, compare]

and user_type =
  | Abstract of Mem_rep.abstract
  | Record of record_type
  | Enum of enum_type
  | User_mono of mono
[@@deriving sexp, equal, hash, compare]

type poly =
  | Mono of mono
  | Forall of Lowercase.t * poly
[@@deriving sexp, equal, hash, compare, variants]

let rec get_mono_from_poly_without_gen = function
  | Mono m -> m
  | Forall (_, p) -> get_mono_from_poly_without_gen p
;;

module Module_path = struct
  include Qualified.Make (Uppercase)

  let append t uppercase =
    let rec inner = function
      | Qualified.Unqualified name ->
        Qualified.Qualified (name, Unqualified uppercase)
      | Qualified (name, rest) -> Qualified.Qualified (name, inner rest)
    in
    inner t
  ;;

  let rec pop = function
    | Qualified.Unqualified _ as x -> x
    | Qualified (name, Unqualified _) -> Qualified.Unqualified name
    | Qualified (name, rest) -> Qualified.Qualified (name, pop rest)
  ;;
end

type 'data module_bindings =
  { path : Uppercase.t Qualified.t
  ; toplevel_vars : (poly * binding_id) list Lowercase.Map.t
  ; toplevel_records : (poly Lowercase.Map.t * type_proof) Lowercase.Set.Map.t
  ; toplevel_fields :
      (type_proof * [ `Mutable | `Immutable ] * poly) Lowercase.Map.t
  ; toplevel_constructors : (poly option * type_proof) Uppercase.Map.t
  ; toplevel_type_constructors : type_id Lowercase.Map.t
  ; toplevel_modules : 'data module_bindings Uppercase.Map.t
  ; opened_modules : 'data module_bindings List.t
  ; signature : unit module_bindings option
  ; data : 'data
  }
[@@deriving sexp, equal, hash, compare, fields]

module Absolute_name = Qualified.Make (Lowercase)

let type_id_of_absolute_name = Absolute_name.hash

let make_type_proof (s : Lowercase.t) mem_rep =
  let absolute_type_name = Qualified.Unqualified s in
  { type_name = s
  ; user_type = Abstract (Mem_rep.Closed mem_rep)
  ; absolute_type_name
  ; ordering = None
  ; tyvar_map = Lowercase.Map.empty
  ; type_id = type_id_of_absolute_name absolute_type_name
  ; mem_rep = Mem_rep.Closed mem_rep
  }
;;

let int_type = make_type_proof "int" `Bits32
let float_type = make_type_proof "float" `Bits64
let bool_type = make_type_proof "bool" `Bits8
let unit_type = make_type_proof "unit" `Bits0
let string_type = make_type_proof "string" `Reg
let char_type = make_type_proof "char" `Bits8

let base_type_map =
  List.map
    [ int_type; float_type; bool_type; unit_type; string_type; char_type ]
    ~f:(fun t -> t.type_id, (None, Abstract t.mem_rep, t))
  |> Int.Map.of_alist_exn
;;

let base_module_bindings empty_data =
  { path = Qualified.Unqualified "Std"
  ; toplevel_vars = Lowercase.Map.empty
  ; toplevel_fields = Lowercase.Map.empty
  ; toplevel_records = Lowercase.Set.Map.empty
  ; toplevel_constructors = Uppercase.Map.empty
  ; toplevel_type_constructors =
      List.map
        [ int_type; float_type; bool_type; unit_type; string_type; char_type ]
        ~f:(fun t -> t.type_name, t.type_id)
      |> Lowercase.Map.of_alist_exn
  ; toplevel_modules = Uppercase.Map.empty
  ; opened_modules = []
  ; data = empty_data
  ; signature = None
  }
;;

let empty_module_bindings path empty_data =
  { path
  ; toplevel_vars = Lowercase.Map.empty
  ; toplevel_fields = Lowercase.Map.empty
  ; toplevel_records = Lowercase.Set.Map.empty
  ; toplevel_constructors = Uppercase.Map.empty
  ; toplevel_type_constructors = Lowercase.Map.empty
  ; toplevel_modules = Uppercase.Map.empty
  ; opened_modules = [ base_module_bindings empty_data ]
  ; signature = None
  ; data = empty_data
  }
;;
