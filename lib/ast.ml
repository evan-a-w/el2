open! Core

type name = string module_path
and upper_name = string module_path
and 'a module_path = 'a

and type_decl =
  [ `Alias of type_expr
  | `Struct of (string * type_expr) list
  | `Enum of (upper_name * type_expr option) list
  ]

and type_expr =
  [ `Unit
  | `Named of name
  | `Named_args of name * type_expr list
  | `Tuple of type_expr list
  | `Function of type_expr * type_expr
  | `Pointer of type_expr
  ]
[@@deriving sexp, compare]
(* for now no modules, but in future will be list of qualifiers then 'a,
   with syntax moda::modb::a *)

type builtin_pattern =
  [ `Unit
  | `Int of int
  | `Null
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of char
  ]
[@@deriving sexp, compare]

type pattern =
  [ builtin_pattern
  | `Var of name
  | `Tuple of pattern list
  | `Enum of upper_name * pattern option
  | `Struct of name (* typename *) * (string * pattern option) list
  | `Typed of pattern * type_expr
  | `Ref of pattern
  ]
[@@deriving sexp, compare]

type var_decl =
  [ `Typed of string * type_expr
  | `Untyped of string
  ]

and expr =
  [ `Unit
  | `Int of int
  | `Null
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of char
  | `Var of name
  | `Assert of expr
  | `Tuple of expr list
  | `Enum of upper_name
  | `Struct of name * (string * expr option) list
  | `Apply of expr * expr
  | `Inf_op of inf_op * expr * expr
  | `Pref_op of pref_op * expr
  | `Deref of expr (* prefix * *)
  | `Ref of expr (* prefix & *)
  | `Tuple_access of expr * int (* postfix . *)
  | `Field_access of expr * string (* postfix . *)
  | `Index of expr * expr (* postfix [] *)
  | `If of expr * expr * expr
  | `Match of expr * (pattern * expr) list
  | `Let of pattern * expr * expr
  | `Assign of expr * expr
  | `Compound of compound_inner list
  | `Typed of expr * type_expr
  | `Unsafe_cast of expr (* sizeof[type_expr] or sizeof(expr) *)
  | `Size_of of [ `Type of type_expr | `Expr of expr ]
  | `Return of expr
  | `Array_lit of
    expr list
  ]

and compound_inner =
  [ `Let of pattern * expr
  | `Expr of expr
  ]

and inf_op =
  [ `Add
  | `Sub
  | `Mul
  | `Div
  | `Rem
  | `Eq
  | `Ne
  | `Ge
  | `Gt
  | `Le
  | `Lt
  | `And
  | `Or
  ]

and pref_op = [ `Minus ]
and type_var = string
and type_decl_name = name * type_var list
and type_def = type_decl_name * type_decl

and toplevel_var =
  [ `Let of pattern * expr
  | `Let_fn of string * var_decl list * expr
  ]

and toplevel =
  [ `Let of pattern * expr
  | `Let_fn of string * var_decl list * expr
  | `Let_type of type_def
  | `Extern of string * type_expr * string
  | `Implicit_extern of string * type_expr * string
  ]
[@@deriving sexp, compare]

let rec pattern_fold_rec pattern ~init ~f =
  let rep = pattern_fold_rec ~f in
  let init =
    match (pattern : pattern) with
    | `Bool _
    | `Var _
    | `Int _
    | `Float _
    | `Char _
    | `String _
    | `Enum _
    | `Null
    | `Unit -> init
    | `Tuple l -> List.fold l ~init ~f:(fun init -> rep ~init)
    | `Ref a | `Typed (a, _) -> rep ~init a
    | `Struct (_, l) ->
      List.fold l ~init ~f:(fun init (_, o) ->
        Option.fold ~init ~f:(fun init -> rep ~init) o)
  in
  f init pattern
;;

let rec expr_fold_rec expr ~init ~f =
  let rep = expr_fold_rec ~f in
  let init =
    match (expr : expr) with
    | `Bool _
    | `Var _
    | `Int _
    | `Float _
    | `Char _
    | `String _
    | `Enum _
    | `Null
    | `Unit -> ()
    | `Tuple l | `Array_lit l -> List.fold l ~init ~f:(fun init -> rep ~init)
    | `Compound l ->
      List.fold l ~init ~f:(fun init ->
          function
          | `Expr e -> rep ~init e
          | `Let (_, e) -> rep ~init e)
    | `Index (a, b)
    | `Inf_op (_, a, b)
    | `Assign (a, b)
    | `Apply (a, b)
    | `Let (_, a, b) -> rep ~init:(rep ~init a) b
    | `Size_of (`Type _) -> ()
    | `Size_of (`Expr a)
    | `Return a
    | `Tuple_access (a, _)
    | `Field_access (a, _)
    | `Assert a
    | `Unsafe_cast a
    | `Ref a
    | `Deref a
    | `Pref_op (_, a)
    | `Typed (a, _) -> rep ~init a
    | `Match (a, l) ->
      let init = rep ~init a in
      List.fold l ~init ~f:(fun init (_, e) -> rep ~init e)
    | `Struct (_, l) ->
      List.fold l ~init ~f:(fun init (_, o) ->
        Option.fold ~init ~f:(fun init -> rep ~init) o)
    | `If (a, b, c) -> rep ~init:(rep ~init:(rep ~init a) b) c
  in
  f init expr
;;
