open! Core
open! Types
open! Typed_ast

(* use CPS style to avoid stack overflows
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
  | Char of char
  | Tuple of value list
  | Array of value list
  | Enum of string * value option
  | Struct of (string * value) list
  | Function of Type_check.var * mono String.Map.t option * (string * mono) list

and value =
  { mutable value : value_inner
  ; mutable mono : mono
  }

let rec equal_value (a : value) (b : value) =
  match a.value, b.value with
  | _, _ when phys_equal a b -> true
  | Unit, Unit -> true
  | Null, Null -> true
  | Int a, Int b -> Int.equal a b
  | Float a, Float b -> Float.equal a b
  | String a, String b -> String.equal a b
  | Bool a, Bool b -> Bool.equal a b
  | Char a, Char b -> Char.equal a b
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

(* using an exception for this makes it very easy to implement! *)
exception Return of value
exception Break of value

let rec eval ~(state : state) ~(var : Type_check.var) ~(f : value -> unit) expr
  : unit
  =
  match Hashtbl.find state.res_cache var.name with
  | Some x -> f x
  | None ->
    eval_expr ~state expr ~f:(fun res ->
      Hashtbl.set state.res_cache ~key:var.name ~data:res;
      f res)

and eval_i64 ~state (expr : Type_check.expr) ~f =
  eval_expr ~state expr ~f:(fun v ->
    match v.value with
    | Int i -> f i
    | _ -> failwith "Expected int")

and eval_bool ~state (expr : Type_check.expr) ~f =
  eval_expr ~state expr ~f:(fun v ->
    match v.value with
    | Bool i -> f i
    | _ -> failwith "Expected booil")

and eval_array_lit ~state (expr : Type_check.expr) ~f =
  eval_expr ~state expr ~f:(fun v ->
    match v.value with
    | Array i -> f i
    | _ -> failwith "Expected array")

and eval_tuple ~state (expr : Type_check.expr) ~f =
  eval_expr ~state expr ~f:(fun v ->
    match v.value with
    | Tuple l -> f l
    | _ -> failwith "Expected tuple")

and eval_list ~state l =
  let r = ref { value = Unit; mono = `Unit } in
  List.map l ~f:(fun expr ->
    eval_expr ~state expr ~f:(fun expr -> r := expr);
    !r)

and eval_named_list ~state l =
  let r = ref { value = Unit; mono = `Unit } in
  List.map l ~f:(fun (name, expr) ->
    eval_expr ~state expr ~f:(fun expr -> r := expr);
    name, !r)

and eval_op ~state ~f (op : Ast.inf_op) a b =
  let ints a b g =
    eval_i64 ~state a ~f:(fun a ->
      eval_i64 ~state b ~f:(fun b -> f { value = g a b; mono = `I64 }))
  in
  let bools a b g =
    eval_bool ~state a ~f:(fun a ->
      eval_bool ~state b ~f:(fun b -> f { mono = `Bool; value = g a b }))
  in
  let values a b g =
    eval_expr ~state a ~f:(fun a ->
      eval_expr ~state b ~f:(fun b -> f { mono = `Bool; value = g a b }))
  in
  match op with
  | `Ge -> ints a b (fun a b -> Bool (a >= b))
  | `Rem -> ints a b (fun a b -> Int (a % b))
  | `Div -> ints a b (fun a b -> Int (a / b))
  | `Eq -> values a b (fun a b -> Bool (equal_value a b))
  | `Gt -> ints a b (fun a b -> Bool (a > b))
  | `Mul -> ints a b (fun a b -> Int (a * b))
  | `Sub -> ints a b (fun a b -> Int (a - b))
  | `Le -> ints a b (fun a b -> Bool (a <= b))
  | `Add -> ints a b (fun a b -> Int (a + b))
  | `Lt -> ints a b (fun a b -> Bool (a < b))
  | `And -> bools a b (fun a b -> Bool (a && b))
  | `Or -> bools a b (fun a b -> Bool (a || b))
  | `Ne -> ints a b (fun a b -> Bool (a <> b))

and eval_expr
  ~(state : state)
  ((expr_inner, mono) : Type_check.expr)
  ~(f : value -> unit)
  : unit
  =
  match expr_inner with
  | `Char c -> f { value = Char c; mono }
  | `Int i -> f { value = Int i; mono }
  | `Float i -> f { value = Float i; mono }
  | `String s -> f { value = String s; mono }
  | `Bool b -> f { value = Bool b; mono }
  | `Null -> f { value = Null; mono }
  | `Unit -> f { value = Unit; mono }
  | `Tuple l -> f { value = Tuple (eval_list ~state l); mono }
  | `Array_lit l -> f { value = Array (eval_list ~state l); mono }
  | `Index (a, b) ->
    eval_array_lit ~state a ~f:(fun a ->
      eval_i64 ~state b ~f:(fun b -> f (List.nth_exn a b)))
  | `Tuple_access (a, i) ->
    eval_tuple ~state a ~f:(fun a -> f (List.nth_exn a i))
  (* special case assign to a var because its only for locals *)
  | `Assign (x, o) ->
    eval_expr ~state x ~f:(fun x ->
      eval_expr ~state o ~f:(fun o ->
        x.value <- o.value;
        f { value = Unit; mono = `Unit }))
  | `Return x -> eval_expr ~state x ~f:(fun x -> raise (Return x))
  | `Access_enum_field (field, x) ->
    eval_expr ~state x ~f:(fun x ->
      match x.value with
      | Enum (name, op) when String.equal name field -> Option.value_exn op |> f
      | _ -> failwith [%string "Expected enum with %{field} tag"])
  | `Compound e ->
    eval_expr ~state e ~f:(fun e ->
      match e.value with
      | Struct l -> f { value = Struct l; mono }
      | _ -> failwith "Expected struct")
  | `Inf_op (op, a, b) -> eval_op ~state ~f op a b
  | `Field_access (a, field) ->
    eval_expr ~state a ~f:(fun a ->
      match a.value with
      | Struct l ->
        (match List.Assoc.find l ~equal:String.equal field with
         | Some x -> f x
         | None -> failwith [%string "Expected field %{field}"])
      | _ -> failwith "Expected struct")
  | `Local_var s ->
    (match Map.find state.locals s with
     | Some x -> f x
     | None -> failwith [%string "Expected local var %{s}"])
  | `Ref _ | `Deref _ -> failwith "not allowed"
  | `Size_of m -> do_size_of ~state m ~f
  | `Assert e ->
    eval_bool ~state e ~f:(fun b -> if not b then failwith "assert")
  | `Break a -> eval_expr ~state a ~f:(fun a -> raise (Break a))
  | `Glob_var (var, o) ->
    let var =
      match var with
      | El v -> v
      | _ -> failwith "Expected el var"
    in
    (match var.args with
     | `Func args -> f { value = Function (var, o, args); mono }
     | `Non_func ->
       let expr = Option.value_exn var.Typed_ast.typed_expr in
       let expr = fst expr, snd expr |> Type_check.poly_inner in
       eval ~state ~var ~f expr)
  | `Pref_op (op, x) ->
    (match op with
     | `Minus ->
       eval_i64 ~state x ~f:(fun x -> f { mono = `I64; value = Int (-x) }))
  | `Struct l -> f { value = Struct (eval_named_list ~state l); mono }
  | `Enum (a, op) ->
    (match op with
     | None -> f { value = Enum (a, None); mono }
     | Some x ->
       eval_expr ~state x ~f:(fun x -> f { value = Enum (a, Some x); mono }))
  | `Loop e ->
    (try eval_expr ~state e ~f:(fun _ -> ()) with
     | Break v -> f v)
  | `Unsafe_cast e -> do_unsafe_cast ~state ~to_:mono e ~f
  | `Check_variant (s, e) ->
    eval_expr ~state e ~f:(fun e ->
      match e.value with
      | Enum (name, _) -> f { value = Bool (String.equal name s); mono = `Bool }
      | _ -> failwith [%string "Expected enum"])
  | `Let (a, b, c) ->
    eval_expr ~state b ~f:(fun b ->
      let state = { state with locals = Map.set state.locals ~key:a ~data:b } in
      eval_expr ~state c ~f)
  | `If (a, b, c) ->
    eval_bool ~state a ~f:(fun a ->
      if a then eval_expr ~state b ~f else eval_expr ~state c ~f)
  | `Apply (a, b) -> do_apply ~state a b ~f mono

and do_size_of ~state m ~f =
  let _ = state, m, f in
  failwith "TODO"

and do_unsafe_cast ~state ~to_ e ~f =
  let _ = state, to_, e, f in
  failwith "TODO"

and do_apply ~state ~f a b res_mono =
  eval_expr ~state b ~f:(fun b ->
    let fargs =
      match b.value with
      | Tuple l -> l
      | _ -> [ b ]
    in
    eval_expr ~state a ~f:(fun a ->
      match a.value with
      | Function (var, _, args) ->
        let locals =
          List.zip_exn args fargs
          |> List.fold ~init:state.locals ~f:(fun acc ((key, _), data) ->
            Map.set acc ~key ~data)
        in
        let state = { state with locals } in
        let expr = Option.value_exn var.Typed_ast.typed_expr in
        let expr = fst expr, res_mono in
        (try eval_expr ~state ~f expr with
         | Return x -> f x
         | _ ->
           print_endline "Failed to eval function";
           Pretty_print.typed_ast expr |> Pretty_print.output_endline)
      | _ -> failwith "Expected function"))
;;

let eval ~state ~var expr =
  let res = ref None in
  eval ~state ~var expr ~f:(fun x -> res := Some x);
  Option.value_exn !res |> expr_of_value
;;
