open! Core
open! Ast
open! Types
open Type_common

type type_check_state =
  [ `Untouched
  | `In_checking
  | `Done
  ]
[@@deriving sexp, compare]

type comptime_var =
  [ `True
  | `False
  | `Var of string * comptime_var option ref
  ]
[@@deriving sexp, compare]

let rec comptime_var_inner x =
  match x with
  | `True | `False | `Var (_, { contents = None }) -> x
  | `Var (_, ({ contents = Some a } as r)) ->
    let res = comptime_var_inner a in
    r := Some res;
    res
;;

let unify_comptime_var ~user ~used =
  let a = comptime_var_inner user in
  let b = comptime_var_inner used in
  match phys_equal a b, a, b with
  | true, _, _ -> ()
  | _, `True, `True | _, `False, `False | _, `False, _ -> ()
  | _, `True, `Var (_, b) -> b := Some `True
  | _, `Var (_, _), `Var (_, _) | _, `Var (_, _), `True -> ()
  | _, `Var (_, b), `False -> b := Some `False
  | _ ->
    [%string
      "Failed to unify comptime vars %{[%sexp (user : comptime_var)]#Sexp} and \
       %{[%sexp (used : comptime_var)]#Sexp}"]
    |> failwith
;;

type scc_state =
  { (* Stuff for Tarjan's SCC algo *)
    mutable index : int option
  ; mutable lowlink : int
  ; mutable on_stack : bool
  }
[@@deriving sexp, compare]

type 'data var =
  { name : string
  ; data : 'data
  ; ty_var_map : mono String.Table.t option [@compare.ignore]
  ; mutable args : [ `Non_func | `Func of (string * mono) list ]
  ; comptime : comptime_var
  ; expr : expanded_expr
  ; mutable typed_expr : 'data gen_expr option
  ; mutable poly : poly
  ; mutable used_globals : String.Set.t
  ; mutable scc : 'data scc
  ; mutable scc_st : scc_state
  ; unique_name : string
  }

and 'data top_var =
  | El of 'data var
  | Extern of string * string * mono
  | Implicit_extern of string * string * mono

and 'data scc =
  { vars : 'data var Stack.t [@compare.ignore]
  ; mutable type_check_state : type_check_state
  }

and var_decl = string * mono

and 'a expr_inner =
  [ `Unit
  | `Null
  | `Int of int
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of string
  | `Glob_var of 'a top_var * mono String.Map.t option
  | `Local_var of string
  | `Tuple of 'a expr list
  | `Enum of string * 'a expr option
  | `Struct of (string * 'a expr) list
  | `Apply of 'a expr * 'a expr
  | `Inf_op of inf_op * 'a expr * 'a expr
  | `Pref_op of pref_op * 'a expr
  | `Deref of 'a expr (* prefix * *)
  | `Ref of 'a expr (* prefix & *)
  | `Tuple_access of 'a expr * int
  | `Field_access of 'a expr * string (* postfix . *)
  | `Index of 'a expr * 'a expr (* postfix [] *)
  | `If of 'a expr * 'a expr * 'a expr
  | (* by here match expressions have been tranformed *)
    (* | `Match of 'a expr * (pattern * 'a expr) list *)
    `Let of
    string * 'a expr * 'a expr
  | `Assign of 'a expr * 'a expr
  | `Compound of 'a expr
  | `Access_enum_field of string * 'a expr
  | `Check_variant of string * 'a expr
  | `Assert of 'a expr
  | `Unsafe_cast of 'a expr
  | `Return of 'a expr
  | `Break of 'a expr
  | `Loop of 'a expr
  | `Array_lit of 'a expr list
  | `Size_of of mono
  ]

and 'a expr = 'a expr_inner * mono
and 'a gen_expr = 'a expr_inner * poly

and 'a mem_assignable_expr =
  [ `Deref of 'a expr
  | `Glob_var of string * mono String.Map.t option ref
  | `Local_var of string
  | `Index of 'a expr * 'a expr
  | `Field_access of 'a expr * string
  ]
[@@deriving sexp, compare]

let rec go_expr_map_rec
  ~user_type_mem
  ((expr_inner : 'a expr_inner), (mono : mono))
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
      `Glob_var (name, Option.map inst_map ~f:(Map.map ~f:mono_f))
    | `Assign (a, b) -> `Assign (f a, f b)
    | `Access_enum_field (en, e) -> `Access_enum_field (en, f e)
    | `Inf_op (a, b, c) -> `Inf_op (a, f b, f c)
    | `Field_access (e, fi) -> `Field_access (f e, fi)
    | `Loop e -> `Loop (f e)
    | `Break e -> `Break (f e)
    | `Ref e -> `Ref (f e)
    | `Deref e -> `Deref (f e)
    | `Pref_op (a, b) -> `Pref_op (a, f b)
    | `Struct l -> `Struct (List.map l ~f:(fun (a, b) -> a, f b))
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

let unify_var_comptimes ~user ~used =
  match user, used with
  | El a, El b -> unify_comptime_var ~user:a.comptime ~used:b.comptime
  | El a, _ -> unify_comptime_var ~user:a.comptime ~used:`False
  | _, El a -> unify_comptime_var ~used:a.comptime ~user:`False
  | _ -> ()
;;

module And = struct
  let ( && ) a b = `Inf_op (`And, a, b), `Bool
end

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

let rec reach_end' ?default ~seen (mono : mono) =
  let rep = reach_end' ?default ~seen in
  let mono = inner_mono mono in
  if Set.mem !seen mono
  then mono
  else (
    seen := Set.add !seen mono;
    match mono with
    | `Bool | `C_int | `I64 | `F64 | `Unit | `Char | `Bottom -> mono
    | `User _ -> mono
    (*
      (match user_type_monify x with
       | Some r -> rep r
       | None -> mono)
     *)
    | `Function (a, b) -> `Function (rep a, rep b)
    | `Opaque x -> rep x
    | `Pointer x -> `Pointer (rep x)
    | `Tuple _ -> mono
    | `Indir _ | `Var _ ->
      (match default with
       | None -> raise (Incomplete_type mono)
       | Some x -> x))
;;

let reach_end ?default mono = reach_end' ?default ~seen:(ref Mono_set.empty) mono

(*
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
    | `User { orig_user_type = { info = { contents = Some (`Enum l) }; _ }; _ }
      ->
      `Enum
        (List.map l ~f:(fun (s, m) ->
           s, Option.map m ~f:(decompose_into_pattern ~make_a)))
    | `User
        { orig_user_type =
            { repr_name; info = { contents = Some (`Struct l) }; _ }
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
 *)

let rec expr_map_monos (expr_inner, mono) ~f =
  let expr_inner =
    match (expr_inner : _ expr_inner) with
    | `Unsafe_cast e -> `Unsafe_cast (expr_map_monos ~f e)
    | `Array_lit l -> `Array_lit (List.map l ~f:(expr_map_monos ~f))
    | `Tuple l -> `Tuple (List.map l ~f:(expr_map_monos ~f))
    | `Compound e -> `Compound (expr_map_monos ~f e)
    | `Loop e -> `Loop (expr_map_monos ~f e)
    | `Break e -> `Break (expr_map_monos ~f e)
    | `Index (a, b) -> `Index (expr_map_monos ~f a, expr_map_monos ~f b)
    | `Tuple_access (a, b) -> `Tuple_access (expr_map_monos ~f a, b)
    | `Glob_var (name, inst_map) ->
      `Glob_var (name, Option.map inst_map ~f:(Map.map ~f))
    | `Assign (a, b) -> `Assign (expr_map_monos ~f a, expr_map_monos ~f b)
    | `Access_enum_field (en, e) -> `Access_enum_field (en, expr_map_monos ~f e)
    | `Inf_op (a, b, c) -> `Inf_op (a, expr_map_monos ~f b, expr_map_monos ~f c)
    | `Field_access (e, fi) -> `Field_access (expr_map_monos ~f e, fi)
    | `Return e -> `Return (expr_map_monos ~f e)
    | `Ref e -> `Ref (expr_map_monos ~f e)
    | `Deref e -> `Deref (expr_map_monos ~f e)
    | `Pref_op (a, b) -> `Pref_op (a, expr_map_monos ~f b)
    | `Struct l ->
      `Struct (List.map l ~f:(fun (a, b) -> a, expr_map_monos ~f b))
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

let var var = El var

let create_func ~name ~expr ~var_decls ~data ~unique_name ~ty_var_map =
  { name
  ; comptime = `Var (name, ref None)
  ; unique_name
  ; ty_var_map
  ; expr
  ; data
  ; args = `Func var_decls
  ; used_globals = String.Set.empty
  ; typed_expr = None
  ; poly =
      (let a = make_indir () in
       let b = make_indir () in
       `Mono (`Function (a, b)))
  ; scc = { vars = Stack.create (); type_check_state = `Untouched }
  ; scc_st = { on_stack = false; lowlink = -1; index = None }
  }
;;

let create_non_func ~name ~expr ~data ~unique_name ~ty_var_map =
  { name
  ; comptime = `Var (name, ref (Some `True))
  ; unique_name
  ; ty_var_map
  ; expr
  ; data
  ; typed_expr = None
  ; args = `Non_func
  ; used_globals = String.Set.empty
  ; poly = `Mono (make_indir ())
  ; scc = { vars = Stack.create (); type_check_state = `Untouched }
  ; scc_st = { on_stack = false; lowlink = -1; index = None }
  }
;;

let unique_name = function
  | Extern (_, unique_name, _)
  | Implicit_extern (_, unique_name, _)
  | El { unique_name; _ } -> unique_name
;;
