open! Core
open! Types
open! Typed_ast

(* use CPS to avoid stack overflows
   might try to experiment with other methods (devirtualization trampolining thingo!)
   but will prob just do that in the el2 compiler
*)

type value_inner =
  | Unit
  | Null
  | Int of int
  | Float of float
  | String of string
  | Bool of bool
  | Char of string
  | Tuple of value list
  | Array of value list
  | Enum of string * value option
  | Struct of (string * value) list
  | Function of
      ((Type_check.var[@sexp.opaque])
      * (mono String.Map.t option[@sexp.opaque])
      * (string * mono) list)

and value =
  { mutable value : value_inner
  ; mutable mono : mono
  }
[@@deriving sexp]

module Cont = struct
  type ('a, 'b) t = ('a -> 'b) -> 'b

  include Monad.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let return x f = f x
      let bind c ~f k = c (fun t -> f t k)
      let map = `Define_using_bind
    end)
end

module Ret = struct
  type 'a t =
    | Value of 'a
    | Break of value
    | Return of value
  [@@deriving sexp]

  include Monad.Make (struct
      type nonrec 'a t = 'a t

      let return x = Value x

      let bind x ~f =
        match x with
        | Value x -> f x
        | Break x -> Break x
        | Return x -> Return x
      ;;

      let map = `Define_using_bind
    end)

  module Cont = struct
    type nonrec ('a, 'b) t = ('a t, 'b t) Cont.t

    include Monad.Make2 (struct
        type nonrec ('a, 'b) t = ('a, 'b) t

        let return x f = f (return x)

        let bind x ~f k =
          x (fun x ->
            match x with
            | Value x -> f x k
            | Break x -> Break x
            | Return x -> Return x)
        ;;

        let map = `Define_using_bind
      end)
  end
end

let rec equal_value (a : value) (b : value) =
  match a.value, b.value with
  | _, _ when phys_equal a b -> true
  | Unit, Unit -> true
  | Null, Null -> true
  | Int a, Int b -> Int.equal a b
  | Float a, Float b -> Float.equal a b
  | String a, String b -> String.equal a b
  | Bool a, Bool b -> Bool.equal a b
  | Char a, Char b -> String.equal a b
  | Tuple a, Tuple b -> List.equal equal_value a b
  | Array a, Array b -> List.equal equal_value a b
  | Enum (a, b), Enum (c, d) -> String.equal a c && Option.equal equal_value b d
  | Struct a, Struct b ->
    List.equal (fun (a, b) (c, d) -> String.equal a c && equal_value b d) a b
  | _ -> false
;;

let rec expr_of_value (value : value) : Type_check.expr =
  let inner : Type_check.expr_inner =
    match value.value with
    | Unit -> `Unit
    | Null -> `Null
    | Int i -> `Int i
    | Float f -> `Float f
    | String s -> `String s
    | Bool b -> `Bool b
    | Char c -> `Char c
    | Tuple l -> `Tuple (List.map l ~f:expr_of_value)
    | Array l -> `Array_lit (List.map l ~f:expr_of_value)
    | Enum (name, op) -> `Enum (name, Option.map op ~f:expr_of_value)
    | Struct l -> `Struct (List.map l ~f:(fun (x, y) -> x, expr_of_value y))
    | Function (var, inst_map, _) -> `Glob_var (El var, inst_map)
  in
  inner, value.mono
;;

type state =
  { locals : value String.Map.t
  ; state : Type_check.Type_state.t
  ; res_cache : value String.Table.t
  }

let make_state (state : Type_check.Type_state.t) : state =
  { state; locals = String.Map.empty; res_cache = String.Table.create () }
;;

open Ret.Cont.Let_syntax

let rec eval ~(state : state) ~(var : Type_check.var) expr =
  match Hashtbl.find state.res_cache var.name with
  | Some x -> return x
  | None ->
    let%map res = eval_expr ~state expr in
    Hashtbl.set state.res_cache ~key:var.name ~data:res;
    res

and eval_i64 ~state (expr : Type_check.expr) =
  match%map eval_expr ~state expr with
  | { value = Int i; _ } -> i
  | _ -> failwith "Expected int"

and eval_bool ~state (expr : Type_check.expr) =
  match%map eval_expr ~state expr with
  | { value = Bool b; _ } -> b
  | _ -> failwith "Expected bool"

and eval_array_lit ~state (expr : Type_check.expr) =
  match%map eval_expr ~state expr with
  | { value = Array b; _ } -> b
  | _ -> failwith "Expected array"

and eval_tuple ~state (expr : Type_check.expr) =
  match%map eval_expr ~state expr with
  | { value = Tuple b; _ } -> b
  | _ -> failwith "Expected tuple"

and eval_list ~state l =
  List.fold_right l ~init:(return []) ~f:(fun expr acc ->
    let%bind acc = acc in
    let%map expr = eval_expr ~state expr in
    expr :: acc)

and eval_named_list ~state l =
  List.fold_right l ~init:(return []) ~f:(fun (name, expr) acc ->
    let%bind acc = acc in
    let%map expr = eval_expr ~state expr in
    (name, expr) :: acc)

and eval_op ~state (op : Ast.inf_op) a b =
  let map_both ~eval ~mono a b g =
    let%bind a = eval ~state a in
    let%map b = eval ~state b in
    { value = g a b; mono }
  in
  let ints = map_both ~eval:eval_i64 ~mono:`I64 in
  let bools = map_both ~eval:eval_bool ~mono:`Bool in
  let values ~mono = map_both ~eval:eval_expr ~mono in
  match op with
  | `Ge -> ints a b (fun a b -> Bool (a >= b))
  | `Rem -> ints a b (fun a b -> Int (a % b))
  | `Div -> ints a b (fun a b -> Int (a / b))
  | `Eq -> values ~mono:`Bool a b (fun a b -> Bool (equal_value a b))
  | `Gt -> ints a b (fun a b -> Bool (a > b))
  | `Mul -> ints a b (fun a b -> Int (a * b))
  | `Sub -> ints a b (fun a b -> Int (a - b))
  | `Le -> ints a b (fun a b -> Bool (a <= b))
  | `Add -> ints a b (fun a b -> Int (a + b))
  | `Lt -> ints a b (fun a b -> Bool (a < b))
  | `And -> bools a b (fun a b -> Bool (a && b))
  | `Or -> bools a b (fun a b -> Bool (a || b))
  | `Ne -> ints a b (fun a b -> Bool (a <> b))

and eval_expr : 'a. state:state -> Type_check.expr -> (value, 'a) Ret.Cont.t =
  fun ~(state : state) ((expr_inner, mono) : Type_check.expr) ->
  match expr_inner with
  | `Char c -> return { value = Char c; mono }
  | `Int i -> return { value = Int i; mono }
  | `Float i -> return { value = Float i; mono }
  | `String s -> return { value = String s; mono }
  | `Bool b -> return { value = Bool b; mono }
  | `Null -> return { value = Null; mono }
  | `Unit -> return { value = Unit; mono }
  | `Tuple l ->
    let%map l = eval_list ~state l in
    { value = Tuple l; mono }
  | `Array_lit l ->
    let%map l = eval_list ~state l in
    { value = Array l; mono }
  | `Index (a, b) ->
    let%bind a = eval_array_lit ~state a in
    let%map b = eval_i64 ~state b in
    List.nth_exn a b
  | `Tuple_access (a, i) ->
    let%map a = eval_tuple ~state a in
    List.nth_exn a i
  (* special case assign to a var because its only for locals *)
  | `Assign (x, o) ->
    let%bind x = eval_expr ~state x in
    let%map o = eval_expr ~state o in
    x.value <- o.value;
    { value = Unit; mono = `Unit }
  | `Access_enum_field (field, x) ->
    let%map x = eval_expr ~state x in
    (match x.value with
     | Enum (name, op) when String.equal name field -> Option.value_exn op
     | _ -> failwith [%string "Expected enum with %{field} tag"])
  | `Compound e -> eval_expr ~state e
  | `Inf_op (op, a, b) -> eval_op ~state op a b
  | `Field_access (a, field) ->
    let%map a = eval_expr ~state a in
    (match a.value with
     | Struct l ->
       (match List.Assoc.find l ~equal:String.equal field with
        | Some x -> x
        | None -> failwith [%string "Expected field %{field}"])
     | _ -> failwith "Expected struct")
  | `Local_var s ->
    (match Map.find state.locals s with
     | Some x -> return x
     | None -> failwith [%string "Expected local var %{s}"])
  | `Ref _ | `Deref _ -> failwith "not allowed"
  | `Size_of m -> do_size_of ~state m
  | `Assert e ->
    let%map b = eval_bool ~state e in
    if not b then failwith "assert" else { value = Unit; mono = `Unit }
  | `Break x ->
    let%bind a = eval_expr ~state x in
    Cont.return @@ Ret.Break a
  | `Return x ->
    let%bind a = eval_expr ~state x in
    Cont.return @@ Ret.Return a
  | `Glob_var (var, o) ->
    let var =
      match var with
      | El v -> v
      | _ -> failwith "Expected el var"
    in
    (match var.args with
     | `Func args -> return { value = Function (var, o, args); mono }
     | `Non_func ->
       let expr = Option.value_exn var.Typed_ast.typed_expr in
       let expr = fst expr, snd expr |> Type_check.poly_inner in
       eval ~state ~var expr)
  | `Pref_op (op, x) ->
    (match op with
     | `Minus ->
       let%map res = eval_i64 ~state x in
       { value = Int (-res); mono = `I64 })
  | `Struct l ->
    let%map l = eval_named_list ~state l in
    { value = Struct l; mono }
  | `Enum (a, op) ->
    (match op with
     | None -> return { value = Enum (a, None); mono }
     | Some x ->
       let%map x = eval_expr ~state x in
       { value = Enum (a, Some x); mono })
  | `Loop e -> eval_loop ~state e
  | `Unsafe_cast e -> do_unsafe_cast ~state ~to_:mono e
  | `Check_variant (s, e) ->
    let%map e = eval_expr ~state e in
    (match e.value with
     | Enum (name, _) -> { value = Bool (String.equal name s); mono = `Bool }
     | _ -> failwith [%string "Expected enum"])
  | `Let (a, b, c) ->
    let%bind b = eval_expr ~state b in
    let state = { state with locals = Map.set state.locals ~key:a ~data:b } in
    eval_expr ~state c
  | `If (a, b, c) ->
    let%bind a = eval_bool ~state a in
    if a then eval_expr ~state b else eval_expr ~state c
  | `Apply (a, b) -> do_apply ~state a b mono

and eval_loop ~state e =
  match%bind.Cont eval_expr ~state e with
  | Ret.Break v -> Cont.return @@ Ret.Value v
  | Ret.Return v -> Cont.return @@ Ret.Return v
  | Ret.Value _ -> eval_loop ~state e

and do_size_of ~state m =
  let _ = state, m in
  failwith "TODO"

and do_unsafe_cast ~state ~to_ e =
  let _ = state, to_, e in
  failwith "TODO"

and do_apply ~state a b res_mono =
  let%bind b = eval_expr ~state b in
  let fargs =
    match b.value with
    | Tuple l -> l
    | _ -> [ b ]
  in
  let%bind a = eval_expr ~state a in
  let var, args =
    match a.value with
    | Function (var, _, args) -> var, args
    | _ -> failwith "Expected function"
  in
  let locals =
    List.zip_exn args fargs
    |> List.fold ~init:state.locals ~f:(fun acc ((key, _), data) ->
      Map.set acc ~key ~data)
  in
  let state = { state with locals } in
  let expr = Option.value_exn var.Typed_ast.typed_expr in
  let expr = fst expr, res_mono in
  match%bind.Cont eval_expr ~state expr with
  | Return x -> return x
  | Value _ as r -> Cont.return r
  | Break _ -> failwith "Not inside loop"
;;

let eval ~state ~var expr =
  let value =
    match eval ~state ~var expr Fn.id with
    | Value x -> x
    | Return x -> x
    | Break x -> x
  in
  expr_of_value value
;;
