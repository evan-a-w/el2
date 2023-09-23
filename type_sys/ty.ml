open! Core
open! Shared
open! Frontend

type variance_map = Variance.t Lowercase.Map.t [@@deriving sexp, equal, compare]

type type_constructor_arg =
  | Tuple_arg of (Variance.t * Lowercase.t) list
  | Single_arg of Variance.t * Lowercase.t
[@@deriving sexp, equal, compare]

let show_type_constructor_arg = function
  | Tuple_arg [ (_, s) ] | Single_arg (_, s) -> s
  | Tuple_arg l -> "(" ^ String.concat ~sep:", " (List.map l ~f:snd) ^ ")"
;;

type type_constructor =
  type_constructor_arg option * user_type * type_proof
  (* replace bound variables in type_constructor_arg with new TyVars when using this mono *)
[@@deriving sexp, equal, compare]

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
  ; type_constructor_arg : type_constructor_arg option
  ; ordering : Lowercase.t list option
  ; tyvar_map : mono Lowercase.Map.t
  ; user_type : user_type
  }
[@@deriving sexp, equal, compare]

and binding_state =
  { name : Lowercase.t
  ; poly : poly
  }
[@@deriving sexp, equal, compare, fields]

and mono =
  (* name and type args *)
  | Weak of Lowercase.t * mono ref
  (* keep track of the path and arg for equality *)
  | Ty_var of Lowercase.t * mono ref
  | Function of mono * mono
  (* closures unify with all closures that have an equivalent mem rep and input/return type *)
  | Closure of mono * mono * closure_info
  | Tuple of mono list
  | Reference of mono
  | Named of type_proof
[@@deriving sexp, equal, compare]

and closure_info =
  { closed_args : (binding_state ref * mono) list
  ; closed_vars : (binding_state ref * mono) list
  }
[@@deriving sexp, equal, compare]

and record_type = (Lowercase.t * (mono * [ `Mutable | `Immutable ])) list
[@@deriving sexp, equal, compare]

and enum_type = (Uppercase.t * mono option) list
[@@deriving sexp, equal, compare]

and user_type =
  | Base of Mem_rep.base
  | Record of record_type
  | Enum of enum_type
  | User_mono of mono
[@@deriving sexp, equal, compare]

and poly =
  | Mono of mono
  | Forall of Lowercase.t * poly
[@@deriving sexp, equal, compare]

let rec condense mono =
  match mono with
  | Weak (_, r) | Ty_var (_, r) ->
    if phys_equal mono !r
    then mono
    else (
      let mono' = condense !r in
      r := mono';
      mono')
  | _ -> mono
;;

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
  { path : Module_path.t
  ; toplevel_vars : (poly * binding_state ref) list Lowercase.Map.t
  ; toplevel_records : (poly Lowercase.Map.t * type_proof) Lowercase.Set.Map.t
  ; toplevel_fields :
      (type_proof * [ `Mutable | `Immutable ] * poly) Lowercase.Map.t
  ; toplevel_constructors : (poly option * type_proof) Uppercase.Map.t
  ; toplevel_types : type_proof Lowercase.Map.t
  ; toplevel_modules : 'data module_bindings Uppercase.Map.t
  ; opened_modules : 'data module_bindings List.t
  ; signature : unit module_bindings option
  ; data : 'data
  }
[@@deriving sexp, equal, compare, fields]

module Absolute_name = Qualified.Make (Lowercase)

let make_type_proof (s : Lowercase.t) mem_rep =
  let absolute_type_name = Qualified.Unqualified s in
  { type_name = s
  ; user_type = Base mem_rep
  ; absolute_type_name
  ; ordering = None
  ; tyvar_map = Lowercase.Map.empty
  ; type_constructor_arg = None
  }
;;

let int_type = make_type_proof "int" `Bits64
let float_type = make_type_proof "float" `Bits64
let bool_type = make_type_proof "bool" `Bits8
let unit_type = make_type_proof "unit" `Bits0
let string_type = make_type_proof "string" `Bits64
let char_type = make_type_proof "char" `Bits8

let base_type_map =
  List.map
    [ int_type; float_type; bool_type; unit_type; string_type; char_type ]
    ~f:(fun t -> t.type_name, t)
  |> Lowercase.Map.of_alist_exn
;;

let base_module_bindings empty_data =
  { path = Qualified.Unqualified "Std"
  ; toplevel_vars = Lowercase.Map.empty
  ; toplevel_fields = Lowercase.Map.empty
  ; toplevel_records = Lowercase.Set.Map.empty
  ; toplevel_constructors = Uppercase.Map.empty
  ; toplevel_modules = Uppercase.Map.empty
  ; toplevel_types = base_type_map
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
  ; toplevel_types = base_type_map
  ; toplevel_modules = Uppercase.Map.empty
  ; opened_modules = [ base_module_bindings empty_data ]
  ; signature = None
  ; data = empty_data
  }
;;

let rec map_free_vars mono ~weak_f ~ty_var_f =
  let go = map_free_vars ~weak_f ~ty_var_f in
  match (mono : mono) with
  | Weak (_, _) | Ty_var (_, _) ->
    let mono = condense mono in
    (match mono with
     | Weak (s, r) -> weak_f (s, r)
     | Ty_var (s, r) -> ty_var_f (s, r)
     | _ -> mono)
  | Function (a, b) -> Function (go a, go b)
  | Closure (a, b, i) ->
    Closure (go a, go b, map_free_vars_closure_info ~weak_f ~ty_var_f i)
  | Tuple l -> Tuple (List.map ~f:go l)
  | Reference x -> Reference (go x)
  | Named type_proof ->
    Named (map_free_vars_type_proof type_proof ~weak_f ~ty_var_f)

and map_free_vars_closure_info { closed_args; closed_vars } ~weak_f ~ty_var_f =
  let go = List.map ~f:(Tuple2.map_snd ~f:(map_free_vars ~weak_f ~ty_var_f)) in
  { closed_args = go closed_args; closed_vars = go closed_vars }

and map_free_vars_type_proof type_proof ~weak_f ~ty_var_f =
  { type_proof with
    tyvar_map =
      Map.map type_proof.tyvar_map ~f:(map_free_vars ~ty_var_f ~weak_f)
  ; user_type = map_free_vars_user_type type_proof.user_type ~weak_f ~ty_var_f
  }

and map_free_vars_user_type user_type ~weak_f ~ty_var_f = failwith "TODO"
