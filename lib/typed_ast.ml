open! Core
open! Ast
open! Types

type name = string module_path
and upper_name = string module_path
and 'a module_path = 'a
(* for now no modules, but in future will be list of qualifiers then 'a,
   with syntax moda::modb::a *)

and var_decl = string * mono

and expr_inner =
  [ `Unit
  | `Null
  | `Int of int
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of char
  | `Glob_var of string * mono String.Map.t option ref (* map for inst vars *)
  | `Local_var of string
  | `Tuple of expr list
  | `Enum of upper_name * expr option
  | `Struct of name * (string * expr) list
  | `Apply of expr * expr
  | `Inf_op of inf_op * expr * expr
  | `Pref_op of pref_op * expr
  | `Deref of expr (* prefix * *)
  | `Ref of expr (* prefix & *)
  | `Tuple_access of expr * int (* postfix . *)
  | `Field_access of expr * string (* postfix . *)
  | `Index of expr * expr (* postfix [] *)
  | `If of expr * expr * expr
  | (* getting this is where we process match expressions *)
    (* | `Match of expr * (pattern * expr) list *)
    `Let of
    string * expr * expr
  | `Assign of expr * expr
  | `Compound of expr
  | `Access_enum_field of string * expr
  | `Check_variant of string * expr
  | `Assert of expr
  | `Unsafe_cast of expr
  | `Return of expr
  | `Array_lit of expr list
  | `Size_of of mono
  ]

and expr = expr_inner * mono
and gen_expr = expr_inner * poly

and mem_assignable_expr =
  [ `Deref of expr
  | `Glob_var of name * mono String.Map.t option ref
  | `Local_var of name
  | `Index of expr * expr
  | `Field_access of expr * string
  ]
[@@deriving sexp, compare]

let rec go_expr_map_rec
  ~user_type_mem
  ((expr_inner : expr_inner), (mono : mono))
  ~on_expr_inner
  ~on_mono
  =
  let f = go_expr_map_rec ~user_type_mem ~on_expr_inner ~on_mono in
  let mono_f =
    go_mono_map_rec
      ~user_type_mem
      ~on_indir:(Fn.const None)
      ~on_var:(Fn.const None)
      ~f:on_mono
  in
  let expr_inner =
    match expr_inner with
    | `Char _
    | `String _
    | `Int _
    | `Bool _
    | `Float _
    | `Unit
    | `Local_var _
    | `Null -> expr_inner
    | `Enum (name, expr) -> `Enum (name, Option.map expr ~f)
    | `Tuple l -> `Tuple (List.map l ~f)
    | `Array_lit l -> `Array_lit (List.map l ~f)
    | `Return e -> `Return (f e)
    | `Size_of m -> `Size_of (mono_f m)
    | `Compound e -> `Compound (f e)
    | `Index (a, b) -> `Index (f a, f b)
    | `Tuple_access (a, b) -> `Tuple_access (f a, b)
    | `Glob_var (name, inst_map) ->
      (match !inst_map with
       | Some x -> inst_map := Some (Map.map ~f:mono_f x)
       | None -> ());
      `Glob_var (name, inst_map)
    | `Assign (a, b) -> `Assign (f a, f b)
    | `Access_enum_field (en, e) -> `Access_enum_field (en, f e)
    | `Inf_op (a, b, c) -> `Inf_op (a, f b, f c)
    | `Field_access (e, fi) -> `Field_access (f e, fi)
    | `Ref e -> `Ref (f e)
    | `Deref e -> `Deref (f e)
    | `Pref_op (a, b) -> `Pref_op (a, f b)
    | `Struct (n, l) -> `Struct (n, List.map l ~f:(fun (a, b) -> a, f b))
    | `Apply (a, b) -> `Apply (f a, f b)
    | `Let (a, b, c) -> `Let (a, f b, f c)
    | `If (a, b, c) -> `If (f a, f b, f c)
    | `Check_variant (variant, expr) -> `Check_variant (variant, f expr)
    | `Assert e -> `Assert (f e)
    | `Unsafe_cast e -> `Unsafe_cast (f e)
  in
  let expr_inner = on_expr_inner expr_inner in
  let mono = mono_f mono in
  expr_inner, mono
;;

let ( && ) a b = `Inf_op (`And, a, b), `Bool

let expr_map_rec expr ~on_expr_inner ~on_mono =
  let user_type_mem = ref String.Map.empty in
  go_expr_map_rec expr ~on_expr_inner ~on_mono ~user_type_mem
;;

type int_range =
  { start : Big_int_Z.big_int
  ; size : Big_int_Z.big_int
  }

type 'a pattern_branches_inner =
  [ `Unit of 'a
  | `Any of 'a
  | `Bool of 'a * 'a
  | `Int of (int_range * 'a) list
  | `Char of (int_range * 'a) list
  | `String of (string * 'a) list
  | `Float of (float * 'a) list
  | `Ref of 'a pattern_branches
  | `Tuple of 'a list
  | `Enum of (string * 'a pattern_branches option) list
  | `Struct of string * (string * 'a pattern_branches) list
  ]

and 'a pattern_branches = 'a pattern_branches_inner * mono

let two_pow i = Big_int_Z.power (Big_int_Z.big_int_of_int 2) i

exception Incomplete_type of mono
exception Cannot_pattern_match of mono

let rec reach_end (mono : mono) =
  let mono = inner_mono mono in
  match mono with
  | `Bool | `C_int | `I64 | `F64 | `Unit | `Char -> mono
  | `User x ->
    (match user_type_monify x with
     | Some r -> reach_end r
     | None -> mono)
  | `Function (a, b) -> `Function (reach_end a, reach_end b)
  | `Opaque x -> reach_end x
  | `Pointer x -> `Pointer (reach_end x)
  | `Tuple l -> `Tuple (List.map l ~f:reach_end)
  | `Indir _ | `Var _ -> raise (Incomplete_type mono)
;;

let rec decompose_into_pattern mono ~make_a : 'a pattern_branches =
  let inner =
    match reach_end mono with
    | `Bool -> `Bool (make_a (), make_a ())
    | `I64 ->
      `Int
        [ ( { start = Big_int_Z.sub_big_int (two_pow 63) Big_int_Z.unit_big_int
            ; size = two_pow 64
            }
          , make_a () )
        ]
    | `Char ->
      `Char
        [ ( { start = Big_int_Z.sub_big_int (two_pow 63) Big_int_Z.unit_big_int
            ; size = two_pow 64
            }
          , make_a () )
        ]
    | `F64 -> `Float []
    | `Unit -> `Unit (make_a ())
    | `Tuple l -> `Tuple (List.map l ~f:(decompose_into_pattern ~make_a))
    | `Pointer x -> `Ref (decompose_into_pattern x ~make_a)
    | `User
        { user_type = Insted { info = { contents = Some (`Enum l) }; _ }; _ } ->
      `Enum
        (List.map l ~f:(fun (s, m) ->
           s, Option.map m ~f:(decompose_into_pattern ~make_a)))
    | `User
        { user_type =
            Insted { repr_name; info = { contents = Some (`Struct l) }; _ }
        ; _
        } ->
      `Struct
        ( repr_name
        , List.map l ~f:(fun (s, m) -> s, decompose_into_pattern m ~make_a) )
    | `User _ -> raise (Incomplete_type mono)
    | `Indir _ | `Var _ -> failwith "impossible"
    | `Function _ | `Opaque _ | `C_int -> raise (Cannot_pattern_match mono)
  in
  inner, mono
;;

let rec expr_map_monos (expr_inner, mono) ~f =
  let expr_inner =
    match (expr_inner : expr_inner) with
    | `Unsafe_cast e -> `Unsafe_cast (expr_map_monos ~f e)
    | `Array_lit l -> `Array_lit (List.map l ~f:(expr_map_monos ~f))
    | `Tuple l -> `Tuple (List.map l ~f:(expr_map_monos ~f))
    | `Compound e -> `Compound (expr_map_monos ~f e)
    | `Index (a, b) -> `Index (expr_map_monos ~f a, expr_map_monos ~f b)
    | `Tuple_access (a, b) -> `Tuple_access (expr_map_monos ~f a, b)
    | `Glob_var (name, inst_map) ->
      (match !inst_map with
       | Some x -> inst_map := Some (Map.map ~f x)
       | None -> ());
      `Glob_var (name, inst_map)
    | `Assign (a, b) -> `Assign (expr_map_monos ~f a, expr_map_monos ~f b)
    | `Access_enum_field (en, e) -> `Access_enum_field (en, expr_map_monos ~f e)
    | `Inf_op (a, b, c) -> `Inf_op (a, expr_map_monos ~f b, expr_map_monos ~f c)
    | `Field_access (e, fi) -> `Field_access (expr_map_monos ~f e, fi)
    | `Return e -> `Return (expr_map_monos ~f e)
    | `Ref e -> `Ref (expr_map_monos ~f e)
    | `Deref e -> `Deref (expr_map_monos ~f e)
    | `Pref_op (a, b) -> `Pref_op (a, expr_map_monos ~f b)
    | `Struct (n, l) ->
      `Struct (n, List.map l ~f:(fun (a, b) -> a, expr_map_monos ~f b))
    | `Apply (a, b) -> `Apply (expr_map_monos ~f a, expr_map_monos ~f b)
    | `Let (a, b, c) -> `Let (a, expr_map_monos ~f b, expr_map_monos ~f c)
    | `If (a, b, c) ->
      `If (expr_map_monos ~f a, expr_map_monos ~f b, expr_map_monos ~f c)
    | `Check_variant (variant, expr) ->
      `Check_variant (variant, expr_map_monos ~f expr)
    | `Assert e -> `Assert (expr_map_monos ~f e)
    | `Size_of m -> `Size_of (f m)
    | `Enum (s, e) -> `Enum (s, Option.map e ~f:(expr_map_monos ~f))
    | `Unit
    | `Null
    | `Int _
    | `Float _
    | `String _
    | `Bool _
    | `Char _
    | `Local_var _ -> expr_inner
  in
  expr_inner, f mono
;;
