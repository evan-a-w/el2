open! Core

type 'a path =
  { module_path : string list
  ; inner : 'a
  }
[@@deriving compare, equal]

let show_path show_a = function
  | { module_path = []; inner } -> show_a inner
  | { module_path; inner } ->
    String.concat ~sep:"." module_path ^ "." ^ show_a inner

let empty_path inner = { module_path = []; inner }

let path_fst = function
  | { module_path = []; inner } -> inner
  | { module_path = a :: _; _ } -> a

let sexp_of_path sexp_of_inner { module_path; inner } =
  Sexp.List
    (sexp_of_inner inner :: List.map module_path ~f:(fun x -> Sexp.Atom x))
;;

let path_of_sexp inner_of_sexp sexp =
  match sexp with
  | Sexp.List (inner :: module_path) ->
    { module_path =
        List.map module_path ~f:(function
          | Sexp.Atom x -> x
          | _ -> failwith "path_of_sexp: expected atom")
    ; inner = inner_of_sexp inner
    }
  | _ -> failwith "path_of_sexp: expected list"
;;

type name = string
and upper_name = string

and type_decl =
  [ `Alias of type_expr
  | `Struct of (string * type_expr) list
  | `Enum of (upper_name * type_expr option) list
  ]

and type_expr =
  [ `Unit
  | `Named of name path
  | `Named_args of name path * type_expr list
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
  | `Char of string
  ]
[@@deriving sexp, compare]

type pattern =
  [ builtin_pattern
  | `Var of name
  | `Tuple of pattern list
  | `Enum of upper_name path * pattern option
  | `Struct of name path (* typename *) * (string * pattern option) list
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
  | `Char of string
  | `Var of name path
  | `Assert of expr
  | `Tuple of expr list
  | `Enum of upper_name path
  | `Struct of name path * (string * expr option) list
  | `Apply of expr * expr
  | `Inf_op of inf_op * expr * expr
  | `Question_mark of expr
  | `Pref_op of pref_op * expr
  | `Deref of expr (* prefix * *)
  | `Ref of expr (* prefix & *)
  | `Tuple_access of expr * int * int option (* postfix . *)
  | `Field_access of expr * string path (* postfix . *)
  | `Index of expr * expr (* postfix [] *)
  | `If of expr * expr * expr
  | `Match of expr * (pattern * expr) list
  | `Loop of expr
  | `Let of pattern * expr * expr
  | `Assign of expr * expr
  | `Compound of compound_inner list
  | `Typed of expr * type_expr
  | `Unsafe_cast of expr (* sizeof[type_expr] or sizeof(expr) *)
  | `Size_of of [ `Type of type_expr | `Expr of expr ]
  | `Return of expr
  | `Break of expr
  | `Array_lit of expr list
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
  | `Open of string list
  | `Open_file of string
  | `Module_decl of string * toplevel list
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
    | `Tuple_access (a, _, _)
    | `Field_access (a, _)
    | `Assert a
    | `Unsafe_cast a
    | `Question_mark a
    | `Break a
    | `Loop a
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
