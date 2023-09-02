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
  [@@deriving sexp, equal, hash, compare]

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
  | Var of Lowercase.t Qualified.t * Ty.binding_id
  | Literal of Literal.t
  | Tuple of expr list Qualified.t
  | Constructor of Uppercase.t Qualified.t
  | Record of expr Lowercase.Map.t Qualified.t
  | Wrapped of expr Qualified.t
[@@deriving sexp, equal, hash, compare]

and binding =
  | Name_binding of Lowercase.t * Ty.binding_id
  | Constructor_binding of Uppercase.t Qualified.t * binding option
  | Literal_binding of Literal.t
  | Record_binding of binding Lowercase.Map.t Qualified.t
  | Tuple_binding of binding list Qualified.t
  | Renamed_binding of binding * Lowercase.t * Ty.binding_id
  | Reference_binding of binding
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
  | Field_access of expr * Lowercase.t Qualified.t
  | Field_set of (expr * Lowercase.t Qualified.t * expr)
  | Match of expr * (binding * expr) list
[@@deriving sexp, equal, hash, compare]

let expr_of_literal x = Node (Literal x), Literal.mono_of_t x

let map_binding_inner ~f = function
  | Name_binding _ as res -> res
  | Constructor_binding (x, y) -> Constructor_binding (x, Option.map ~f y)
  | Literal_binding _ as res -> res
  | Record_binding x ->
    Record_binding (Qualified.map x ~f:(Lowercase.Map.map ~f))
  | Tuple_binding x -> Tuple_binding (Qualified.map x ~f:(List.map ~f))
  | Renamed_binding (x, y, z) -> Renamed_binding (f x, y, z)
  | Reference_binding x -> Reference_binding (f x)
;;

let map_binding_inner_m ~f =
  let open State.Result.Let_syntax in
  function
  | Name_binding _ as res -> return res
  | Constructor_binding (x, y) ->
    let%map y =
      match y with
      | Some y ->
        let%map y = f y in
        Some y
      | None -> return None
    in
    Constructor_binding (x, y)
  | Literal_binding x -> return @@ Literal_binding x
  | Record_binding x ->
    let%map map =
      Qualified.map_m
        x
        ~f:
          (Map.fold ~init:(return Lowercase.Map.empty) ~f:(fun ~key ~data acc ->
             let%bind acc = acc in
             let%map data = f data in
             Map.add_exn acc ~key ~data))
    in
    Record_binding map
  | Tuple_binding x ->
    let%map list =
      Qualified.map_m x ~f:(fun l -> State.Result.all @@ List.map l ~f)
    in
    Tuple_binding list
  | Renamed_binding (x, y, z) ->
    let%map x = f x in
    Renamed_binding (x, y, z)
  | Reference_binding x ->
    let%map x = f x in
    Reference_binding x
;;

module Type_def = struct
  type t =
    { type_def : Ty.user_type
    ; type_binding : Ast.Type_binding.t
    ; type_proof : Ty.type_proof
    }
  [@@deriving sexp, equal, hash, compare]
end

type toplevel_type =
  | Sig_binding of binding * Ty.poly
  | Sig_module of module_description
  | Sig_type_def of Type_def.t
[@@deriving sexp, equal, hash, compare]

and module_sig = toplevel_type list [@@deriving sexp, equal, hash, compare]

and module_description =
  { module_name : Uppercase.t Qualified.t
  ; functor_args : (Uppercase.t * module_sig) list
  }
[@@deriving sexp, equal, hash, compare]

type toplevel =
  | Type_def of Type_def.t
  | Let of let_def
  | Module_def of module_def
[@@deriving sexp, equal, hash, compare]

and module_ = module_impl Ty.module_bindings
[@@deriving sexp, equal, hash, compare]

and module_def = module_description * module_
[@@deriving sexp, equal, hash, compare]

and module_impl =
  | Here of toplevel list
  | There of module_
[@@deriving sexp, equal, hash, compare]

let empty_data = Here []

let rec map_let_def_monos_m ~f (let_def : let_def) =
  let open State.Result.Let_syntax in
  match let_def with
  | Rec l ->
    let%map l = State.Result.all @@ List.map l ~f:(on_each_binding ~f) in
    Rec l
  | Nonrec (a, b) ->
    let%map x = on_each_binding ~f (a, b) in
    Nonrec x

and on_each_binding ~f (a, b) =
  let%map.State.Result b = map_expr_monos_m ~f b in
  a, b

and map_expr_monos_m ~f ((expr_inner, mono) : expr) =
  let open State.Result.Let_syntax in
  let%bind mono = f mono in
  let%map expr_inner =
    match expr_inner with
    | Node n ->
      let%map n = map_node_monos_m ~f n in
      Node n
    | If (a, b, c) ->
      let%bind a = map_expr_monos_m ~f a in
      let%bind b = map_expr_monos_m ~f b in
      let%map c = map_expr_monos_m ~f c in
      If (a, b, c)
    | Lambda (a, b) ->
      let%map b = map_expr_monos_m ~f b in
      Lambda (a, b)
    | App (a, b) ->
      let%bind a = map_expr_monos_m ~f a in
      let%map b = map_expr_monos_m ~f b in
      App (a, b)
    | Let_in (l, e) ->
      let%bind l = map_let_def_monos_m ~f l in
      let%map e = map_expr_monos_m ~f e in
      Let_in (l, e)
    | Ref e ->
      let%map e = map_expr_monos_m ~f e in
      Ref e
    | Deref e ->
      let%map e = map_expr_monos_m ~f e in
      Deref e
    | Field_access (e, s) ->
      let%map e = map_expr_monos_m ~f e in
      Field_access (e, s)
    | Field_set (a, b, c) ->
      let%bind a = map_expr_monos_m ~f a in
      let%map c = map_expr_monos_m ~f c in
      Field_set (a, b, c)
    | Match (e, binding_list) ->
      let%bind e = map_expr_monos_m ~f e in
      let%map binding_list =
        State.Result.all @@ List.map binding_list ~f:(on_each_binding ~f)
      in
      Match (e, binding_list)
  in
  expr_inner, mono

and map_node_monos_m ~f (node : node) =
  let open State.Result.Let_syntax in
  match node with
  | Wrapped e ->
    let%map inner = Qualified.map_m e ~f:(map_expr_monos_m ~f) in
    Wrapped inner
  | Tuple l ->
    let%map inner =
      Qualified.map_m l ~f:(fun l ->
        State.Result.all @@ List.map l ~f:(map_expr_monos_m ~f))
    in
    Tuple inner
  | Record m ->
    let%map m =
      Qualified.map_m m ~f:(fun m ->
        Map.fold m ~init:(return Lowercase.Map.empty) ~f:(fun ~key ~data acc ->
          let%bind acc = acc in
          let%map data = map_expr_monos_m ~f data in
          Map.set acc ~key ~data))
    in
    Record m
  | Var (_, _) | Literal _ | Constructor _ -> return node
;;

(* TODO: pretty print typed ast*)
