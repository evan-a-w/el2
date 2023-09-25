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

type base_mem_rep =
  [ `Bits0
  | `Bits8
  | `Bits16
  | `Bits32
  | `Bits64
  ]
[@@deriving sexp, equal, compare]

type type_constructor = type_constructor_arg option * user_type * type_proof
[@@deriving sexp, equal, compare]

and type_proof =
  { type_name : Lowercase.t
  ; mutable indirection : type_proof option
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

and ty_var =
  { ty_var_name : string
  ; equiv_mono : mono ref
  ; equiv_mem_rep : mem_rep
  ; typ : [ `Weak | `Ty_var ]
  }
[@@deriving sexp, equal, compare]

and mono =
  (* name and type args *)
  | Weak of ty_var
  (* keep track of the path and arg for equality *)
  | Ty_var of ty_var
  (* closures unify with all closures that have an equivalent mem rep and input/return type *)
  | Closure of mono * mono * closure_info
  | Tuple of mono list
  | Reference of mono
  | Named of type_proof
[@@deriving sexp, equal, compare]

and mem_rep =
  [ base_mem_rep
  | `Var of mem_rep ref
  | `Sum of mem_rep list
  | `Product of mem_rep list
  ]
[@@deriving sexp, equal, compare]

and closure_info =
  { closed_vars : (binding_state ref * mono * [ `Arg | `Var ]) list }
[@@deriving sexp, equal, compare]

and record_type = (Lowercase.t * (mono * [ `Mutable | `Immutable ])) list
[@@deriving sexp, equal, compare]

and enum_type = (Uppercase.t * mono option) list
[@@deriving sexp, equal, compare]

and user_type =
  | Base of base_mem_rep
  | Record of record_type
  | Enum of enum_type
  | User_mono of mono
[@@deriving sexp, equal, compare]

and poly =
  | Mono of mono
  | Forall of Lowercase.t * poly
[@@deriving sexp, equal, compare]

let rec condense_type_proof (type_proof : type_proof) : type_proof =
  match type_proof.indirection with
  | None -> type_proof
  | Some type_proof' when phys_equal type_proof' type_proof -> type_proof
  | Some type_proof' ->
    if phys_equal type_proof type_proof'
    then type_proof
    else (
      let type_proof' = condense_type_proof type_proof' in
      type_proof.indirection <- Some type_proof';
      type_proof')
;;

let rec condense mono =
  match mono with
  | Weak { equiv_mono; _ } | Ty_var { equiv_mono; _ } ->
    if phys_equal mono !equiv_mono
    then mono
    else (
      let mono' = condense !equiv_mono in
      equiv_mono := mono';
      mono')
  | Named type_proof -> Named (condense_type_proof type_proof)
  | _ -> mono
;;

let rec condense_mem_rep (mem_rep : mem_rep) : mem_rep =
  match mem_rep with
  | `Var r ->
    if phys_equal mem_rep !r
    then mem_rep
    else (
      let mem_rep' = condense_mem_rep !r in
      r := mem_rep';
      mem_rep')
  | _ -> mem_rep
;;

let same_type_proof a b = Qualified.equal Lowercase.equal a.absolute_type_name b.absolute_type_name

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
  ; indirection = None
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

(* f takes `Weak or `Ty_var and returns new thing - we make a ref to that and memoise*)
let rec map_free_vars mono ~f =
  let go = map_free_vars ~f in
  match (mono : mono) with
  | Weak _ | Ty_var _ ->
    let mono = condense mono in
    (match mono with
     | Weak ty_var -> f mono (`Weak ty_var)
     | Ty_var ty_var -> f mono (`Ty_var ty_var)
     | _ -> map_free_vars ~f mono)
  | Closure (a, b, i) -> Closure (go a, go b, map_free_vars_closure_info ~f i)
  | Tuple l -> Tuple (List.map ~f:go l)
  | Reference x -> Reference (go x)
  | Named type_proof -> Named (map_free_vars_type_proof type_proof ~f)

and map_free_vars_closure_info { closed_vars } ~f =
  { closed_vars = List.map ~f:(Tuple3.map_snd ~f:(map_free_vars ~f)) closed_vars
  }

and map_free_vars_type_proof type_proof ~f =
  { type_proof with
    tyvar_map = Map.map type_proof.tyvar_map ~f:(map_free_vars ~f)
  ; user_type = map_free_vars_user_type type_proof.user_type ~f
  }

and map_free_vars_user_type user_type ~f =
  match user_type with
  | Base _ -> user_type
  | Record l ->
    Record (List.map l ~f:(fun (a, (m, c)) -> a, (map_free_vars m ~f, c)))
  | Enum l ->
    Enum (List.map l ~f:(Tuple2.map_snd ~f:(Option.map ~f:(map_free_vars ~f))))
  | User_mono m -> User_mono (map_free_vars ~f m)
;;

let free_ty_vars mono =
  let set = ref String.Set.empty in
  let f mono = function
    | `Weak _ -> mono
    | `Ty_var { ty_var_name = s; _ } ->
      set := Set.add !set s;
      mono
  in
  let _ = map_free_vars mono ~f in
  !set
;;

let log2_ceil x =
  let rec go num_bits pow_two =
    if pow_two >= x then num_bits else go (num_bits + 1) (pow_two * 2)
  in
  go 0 1
;;

let rec mem_rep_of_mono : mono -> mem_rep = function
  | Weak { equiv_mem_rep; _ } | Ty_var { equiv_mem_rep; _ } ->
    condense_mem_rep equiv_mem_rep
  | Closure (_, _, closure_info) -> mem_rep_of_closure_info closure_info
  | Tuple l ->
    let list = List.map l ~f:mem_rep_of_mono in
    `Product list
  | Reference _ -> `Bits64
  | Named t -> mem_rep_of_user_type t.user_type

and mem_rep_of_closure_info { closed_vars } =
  let closed =
    List.map closed_vars ~f:(fun (_, mono, _) -> mem_rep_of_mono mono)
  in
  match closed with
  | [] -> `Bits64
  | _ -> `Product (`Bits64 :: closed)

and mem_rep_of_user_type : user_type -> mem_rep = function
  | Base m -> (m :> mem_rep)
  | Record r ->
    `Product (List.map r ~f:(fun (_, (mono, _)) -> mem_rep_of_mono mono))
  | User_mono m -> mem_rep_of_mono m
  | Enum l ->
    let size = ref 0 in
    let l =
      List.filter_map l ~f:(fun (_, mono_option) ->
        incr size;
        Option.map ~f:mem_rep_of_mono mono_option)
    in
    let discriminant =
      match log2_ceil !size with
      | _ -> `Bits64
    in
    (match l with
     | [] -> discriminant
     | _ -> `Product [ discriminant; `Sum l ])
;;
