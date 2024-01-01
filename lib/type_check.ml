open! Core
open! Ast
open! Types

type unification_error =
  | Failed_to_match of
      { sub : unification_error
      ; failed : mono * mono
      }
  | End
[@@deriving sexp]

let rec show_unification_error = function
  | Failed_to_match { sub; failed = a, b } ->
    [%string
      {| Failed to match %{a |> show_mono} and %{b |> show_mono} because %{show_unification_error sub} |}]
  | End -> "End"
;;

exception Duplicate_type_name of string
exception Duplicate_field of string
exception Duplicate_variant of string
exception Unknown_type of string
exception No_type_args of string list
exception Refutable_pattern of string
exception Unbound_var of string
exception Unification_error of unification_error

type expanded_expr =
  [ `Unit
  | `Null
  | `Int of int
  | `Float of float
  | `String of string
  | `Bool of bool
  | `Char of char
  | `Var of name
  | `Tuple of expanded_expr list
  | `Array_lit of expanded_expr list
  | `Enum of upper_name
  | `Struct of name * (string * expanded_expr option) list
  | `Apply of expanded_expr * expanded_expr
  | `Inf_op of inf_op * expanded_expr * expanded_expr
  | `Pref_op of pref_op * expanded_expr
  | `Deref of expanded_expr (* prefix * *)
  | `Ref of expanded_expr (* prefix & *)
  | `Tuple_access of expanded_expr * int (* postfix . *)
  | `Field_access of expanded_expr * string (* postfix . *)
  | `Index of expanded_expr * expanded_expr (* postfix [] *)
  | `If of expanded_expr * expanded_expr * expanded_expr
  | `Match of expanded_expr * (pattern * expanded_expr) list
  | `Let of string * expanded_expr * expanded_expr
  | `Assign of expanded_expr * expanded_expr
  | `Compound of expanded_expr
  | `Size_of of [ `Type of type_expr | `Expr of expanded_expr ]
  | `Return of expanded_expr
  | `Typed of expanded_expr * type_expr
  | `Assert_struct of string * expanded_expr
  | `Assert_empty_enum_field of string * expanded_expr
  | `Access_enum_field of string * expanded_expr
  | `Unsafe_cast of expanded_expr
  ]
[@@deriving sexp, compare]

module Var = struct
  type type_check_state =
    [ `Untouched
    | `In_checking
    | `Done
    ]
  [@@deriving sexp, compare, variants]

  type scc_state =
    { (* Stuff for Tarjan's SCC algo *)
      mutable index : int option
    ; mutable lowlink : int
    ; mutable on_stack : bool
    }
  [@@deriving sexp, compare]

  type var =
    { name : string
    ; mutable args : [ `Non_func | `Func of (string * mono) list ]
    ; expr : expanded_expr
    ; mutable typed_expr : Typed_ast.gen_expr option
    ; mutable poly : poly
    ; mutable used_globals : String.Set.t
    ; mutable scc : scc
    ; mutable scc_st : scc_state
    }

  and t =
    | El of var
    | Extern of string * string * mono
    | Implicit_extern of string * string * mono

  and scc =
    { vars : var Stack.t [@compare.ignore]
    ; mutable type_check_state : type_check_state
    }
  [@@deriving sexp, compare]

  let t var = El var

  let create_func ~ty_var_counter:_ ~name ~expr ~var_decls =
    { name
    ; expr
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

  let create_non_func ~ty_var_counter:_ ~name ~expr =
    { name
    ; expr
    ; typed_expr = None
    ; args = `Non_func
    ; used_globals = String.Set.empty
    ; poly = `Mono (make_indir ())
    ; scc = { vars = Stack.create (); type_check_state = `Untouched }
    ; scc_st = { on_stack = false; lowlink = -1; index = None }
    }
  ;;
end

let get_user_type_field user_type field =
  match !(user_type.info) with
  | Some (`Struct l) ->
    List.find l ~f:(fun (a, _) -> String.equal a field)
    |> Option.map ~f:Tuple2.get2
  | _ -> None
;;

let get_user_type_variant user_type variant =
  match !(user_type.info) with
  | Some (`Enum l) ->
    List.find l ~f:(fun (a, _) -> String.equal a variant)
    |> Option.map ~f:Tuple2.get2
  | _ -> None
;;

module Type_state = struct
  module T = struct
    type t =
      { glob_vars : Var.t String.Table.t
      ; types : user_type String.Table.t
      ; ty_var_counter : Counter.t
      ; var_counter : Counter.t
      ; variant_to_type : user_type String.Table.t
      ; field_to_type : user_type String.Table.t
      ; locals : mono String.Map.t
      ; ty_vars : mono String.Map.t
      }
    [@@deriving sexp]
  end

  include T

  let default_types () = String.Table.of_alist_exn []

  let create () =
    { glob_vars = String.Table.create ()
    ; types = default_types ()
    ; ty_var_counter = Counter.create ()
    ; var_counter = Counter.create ()
    ; variant_to_type = String.Table.create ()
    ; field_to_type = String.Table.create ()
    ; locals = String.Map.empty
    ; ty_vars = String.Map.empty
    }
  ;;
end

let make_user_type ~repr_name ~ty_vars = { repr_name; ty_vars; info = ref None }

type ty_var_map = mono String.Map.t [@@deriving sexp]
type locals_map = mono String.Map.t

let empty_ty_vars : ty_var_map = String.Map.empty

let get_non_user_type ~make_ty_vars ~state name =
  match name with
  | "i64" -> `I64
  | "c_int" -> `C_int
  | "f64" -> `F64
  | "bool" -> `Bool
  | "char" -> `Char
  | "unit" -> `Unit
  | "_" when make_ty_vars -> make_indir ()
  | _ ->
    (match Map.find state.Type_state.ty_vars name with
     | None -> raise (Unknown_type name)
     | Some a -> a)
;;

let lookup_user_type ~state name =
  match Hashtbl.find state.Type_state.types name with
  | None -> raise (Unknown_type name)
  | Some a -> a
;;

let lookup_mono ~make_ty_vars ~state name =
  try
    let r = lookup_user_type ~state name in
    match r.ty_vars with
    | [] -> `User (inst_user_type_gen r)
    | _ -> raise (No_type_args r.ty_vars)
  with
  | Unknown_type _ -> get_non_user_type ~make_ty_vars ~state name
;;

let rec mono_of_type_expr ?(make_ty_vars = true) ~state (type_expr : type_expr)
  : mono
  =
  let f = mono_of_type_expr ~state in
  match type_expr with
  | `Unit -> `Unit
  | `Named s -> lookup_mono ~make_ty_vars ~state s
  | `Pointer m -> `Pointer (f m)
  | `Tuple l -> `Tuple (List.map l ~f)
  | `Named_args (s, l) ->
    let monos = List.map l ~f in
    `User (lookup_user_type ~state s |> inst_user_type ~monos)
  | `Function (a, b) -> `Function (f a, f b)
;;

let all_user_of_enum ~state l =
  let variants = String.Hash_set.create () in
  ( `Enum
      (List.map l ~f:(fun (s, t) ->
         if Hash_set.mem variants s then raise (Duplicate_variant s);
         let mono_opt =
           Option.map t ~f:(mono_of_type_expr ~make_ty_vars:false ~state)
         in
         Hash_set.add variants s;
         s, mono_opt))
  , variants )
;;

let all_user_of_struct ~state l =
  let set = Hash_set.create (module String) in
  ( `Struct
      (List.map l ~f:(fun (s, t) ->
         if Hash_set.mem set s then raise (Duplicate_field s);
         Hash_set.add set s;
         s, mono_of_type_expr ~make_ty_vars:false ~state t))
  , set )
;;

let process_types ~(state : Type_state.t) types =
  Hashtbl.iteri state.types ~f:(fun ~key ~data:user_type ->
    let ty_vars, decl = Hashtbl.find_exn types key in
    let ty_vars =
      List.fold ty_vars ~init:empty_ty_vars ~f:(fun acc s ->
        let mono = make_var_mono s in
        Map.add_exn acc ~key:s ~data:mono)
    in
    let state = { state with ty_vars } in
    let all_user =
      match decl with
      | `Alias type_expr -> `Alias (mono_of_type_expr ~state type_expr)
      | `Enum l ->
        let all_user, variants = all_user_of_enum ~state l in
        Hash_set.iter variants ~f:(fun s ->
          match Hashtbl.add state.variant_to_type ~key:s ~data:user_type with
          | `Ok -> ()
          | `Duplicate -> raise (Duplicate_variant s));
        all_user
      | `Struct l ->
        let all_user, fields = all_user_of_struct ~state l in
        Hash_set.iter fields ~f:(fun s ->
          match Hashtbl.add state.field_to_type ~key:s ~data:user_type with
          | `Ok -> ()
          | `Duplicate -> raise (Duplicate_variant s));
        all_user
    in
    user_type.info := Some all_user);
  Hashtbl.iter state.types ~f:(fun user_type ->
    user_type.info
    := Option.map
         !(user_type.info)
         ~f:
           (go_all_user_map_rec
              ~f:(function
                | `User x as user ->
                  ignore (get_user_type x);
                  user
                | o -> o)
              ~on_var:(Fn.const None)
              ~on_indir:(Fn.const None)
              ~user_type_mem:(ref String.Map.empty)))
;;

let unique_name counter = "internal_" ^ Counter.next_num counter

let rec breakup_patterns ~counter ~vars (pattern : pattern) (expr : expr) =
  let rep = breakup_patterns ~counter ~vars in
  let enqueue_new expanded_expr =
    let var = unique_name counter in
    Stack.push vars (var, expanded_expr);
    var
  in
  match pattern with
  | `Bool _ | `Float _ | `Char _ | `String _ | `Int _ | `Null ->
    raise (Refutable_pattern (Sexp.to_string_hum [%sexp (pattern : pattern)]))
  | `Var name -> Stack.push vars (name, expand_expr ~counter expr)
  | `Unit ->
    (ignore : string -> unit)
      (enqueue_new (`Typed (expand_expr ~counter expr, `Unit)))
  | `Tuple l ->
    let var = enqueue_new (expand_expr ~counter expr) in
    List.iteri l ~f:(fun i p ->
      let expr = `Tuple_access (`Var var, i) in
      rep p expr)
  | `Ref p ->
    let var = enqueue_new (expand_expr ~counter expr) in
    rep p (`Deref (`Var var))
  | `Struct (type_name, l) ->
    let var =
      enqueue_new (`Assert_struct (type_name, expand_expr ~counter expr))
    in
    List.iter l ~f:(fun (field, opt_p) ->
      let expr = `Field_access (`Var var, field) in
      let p = Option.value opt_p ~default:(`Var field) in
      rep p expr)
  | `Typed (p, type_expr) ->
    let var = enqueue_new (`Typed (expand_expr ~counter expr, type_expr)) in
    rep p (`Var var)
  | `Enum (name, opt_p) ->
    (match opt_p with
     | Some p ->
       let var =
         enqueue_new (`Access_enum_field (name, expand_expr ~counter expr))
       in
       rep p (`Var var)
     | None ->
       (ignore : string -> unit)
         (enqueue_new
            (`Assert_empty_enum_field (name, expand_expr ~counter expr))))

and expand_let ~counter ~init (p, a) =
  let vars = Stack.create () in
  breakup_patterns ~counter ~vars p a;
  Stack.fold vars ~init ~f:(fun acc (var, expr) -> `Let (var, expr, acc))

and expand_expr ~counter (expr : expr) : expanded_expr =
  let f = expand_expr ~counter in
  match (expr : expr) with
  | `Null -> `Null
  | `Unit -> `Unit
  | `Bool b -> `Bool b
  | `Var s -> `Var s
  | `Int i -> `Int i
  | `Float f -> `Float f
  | `Char c -> `Char c
  | `String s -> `String s
  | `Enum s -> `Enum s
  | `Array_lit l -> `Array_lit (List.map l ~f)
  | `Tuple l -> `Tuple (List.map l ~f)
  | `Compound l ->
    let expr =
      List.fold_right l ~init:None ~f:(fun x acc ->
        match x, acc with
        | `Expr e, None -> Some (f e)
        | `Expr e, Some r -> `Let ("_", f e, r) |> Option.some
        | `Let (a, b), None ->
          expand_let ~counter ~init:`Unit (a, b) |> Option.some
        | `Let (a, b), Some r ->
          expand_let ~counter ~init:r (a, b) |> Option.some)
      |> Option.value ~default:`Unit
    in
    `Compound expr
  | `Index (a, b) -> `Index (f a, f b)
  | `Inf_op (op, a, b) -> `Inf_op (op, f a, f b)
  | `Assign (a, b) -> `Assign (f a, f b)
  | `Apply (a, b) -> `Apply (f a, f b)
  | `Tuple_access (a, i) -> `Tuple_access (f a, i)
  | `Field_access (a, field) -> `Field_access (f a, field)
  | `Size_of (`Type t) -> `Size_of (`Type t)
  | `Size_of (`Expr e) -> `Size_of (`Expr (f e))
  | `Return a -> `Return (f a)
  | `Ref a -> `Ref (f a)
  | `Deref a -> `Deref (f a)
  | `Pref_op (op, a) -> `Pref_op (op, f a)
  | `Typed (a, type_expr) -> `Typed (f a, type_expr)
  | `Match (a, l) -> `Match (f a, List.map l ~f:(Tuple2.map_snd ~f))
  | `Struct (name, l) ->
    `Struct (name, List.map l ~f:(Tuple2.map_snd ~f:(Option.map ~f)))
  | `If (a, b, c) -> `If (f a, f b, f c)
  | `Unsafe_cast x -> `Unsafe_cast (f x)
  | `Let (p, a, b) ->
    let init = expand_expr ~counter b in
    expand_let ~counter ~init (p, a)
;;

let function_arg_set ~init l =
  List.fold l ~init ~f:(fun acc ->
      function
      | `Untyped s -> Set.add acc s
      | `Typed (s, _) -> Set.add acc s)
;;

let rec pattern_vars p ~locals =
  match p with
  | `Bool _ | `Float _ | `Char _ | `String _ | `Int _ | `Null -> locals
  | `Var s -> Set.add locals s
  | `Unit -> locals
  | `Tuple l ->
    List.fold l ~init:locals ~f:(fun locals p -> pattern_vars p ~locals)
  | `Ref p -> pattern_vars p ~locals
  | `Struct (_, l) ->
    List.fold l ~init:locals ~f:(fun acc (f, p) ->
      match p with
      | Some p -> pattern_vars p ~locals:acc
      | None -> Set.add acc f)
  | `Typed (p, _) -> pattern_vars p ~locals
  | `Enum (_, p) ->
    (match p with
     | Some p -> pattern_vars p ~locals
     | None -> locals)
;;

let rec traverse_expr
  ~glob_vars
  ~not_found_vars
  ~edge
  ~locals
  (expr : expanded_expr)
  =
  let rep = traverse_expr ~glob_vars ~not_found_vars ~edge in
  match expr with
  | `Bool _ | `Int _ | `Float _ | `Char _ | `String _ | `Enum _ | `Unit | `Null
  | `Size_of (`Type _) -> ()
  | `Var name' ->
    (match Set.mem locals name' with
     | true -> ()
     | false ->
       Var.(edge.used_globals <- Set.add edge.used_globals name');
       if not (Hashtbl.mem glob_vars name')
       then Hash_set.add not_found_vars name')
  | `Match (a, l) ->
    rep ~locals a;
    List.iter l ~f:(fun (p, e) -> rep ~locals:(pattern_vars p ~locals) e)
  | `Tuple l | `Array_lit l -> List.iter l ~f:(rep ~locals)
  | `Index (a, b) | `Inf_op (_, a, b) | `Assign (a, b) | `Apply (a, b) ->
    rep ~locals a;
    rep ~locals b
  | `Let (s, a, b) ->
    let locals = Set.add locals s in
    let rep = rep ~locals in
    rep a;
    rep b
  | `Compound a
  | `Return a
  | `Size_of (`Expr a)
  | `Unsafe_cast a
  | `Assert_struct (_, a)
  | `Access_enum_field (_, a)
  | `Assert_empty_enum_field (_, a)
  | `Tuple_access (a, _)
  | `Field_access (a, _)
  | `Ref a
  | `Deref a
  | `Pref_op (_, a)
  | `Typed (a, _) -> rep ~locals a
  | `Struct (_, l) ->
    List.iter l ~f:(fun (field_name, o) ->
      match o with
      | Some p -> rep ~locals p
      | None -> rep ~locals (`Var field_name))
  | `If (a, b, c) ->
    rep ~locals a;
    rep ~locals b;
    rep ~locals c
;;

let process_toplevel_graph (toplevels : toplevel list) =
  let state = Type_state.create () in
  let type_defs = String.Table.create () in
  let not_found_vars = String.Hash_set.create () in
  let find_references ~edge ~locals expr =
    let open Var in
    match Hashtbl.find state.glob_vars edge.name with
    | Some _ -> raise (Duplicate_type_name edge.name)
    | None ->
      Hashtbl.add_exn state.glob_vars ~key:edge.name ~data:(Var.El edge);
      Hash_set.remove not_found_vars edge.name;
      traverse_expr
        ~glob_vars:state.glob_vars
        ~not_found_vars
        ~edge
        ~locals
        expr
  in
  let let_toplevels = Queue.create () in
  List.iter toplevels ~f:(function
    | `Let_type ((repr_name, ty_vars), type_decl) ->
      (match
         Hashtbl.add
           state.types
           ~key:repr_name
           ~data:(make_user_type ~repr_name ~ty_vars)
       with
       | `Ok ->
         Hashtbl.add_exn type_defs ~key:repr_name ~data:(ty_vars, type_decl)
       | `Duplicate -> raise (Duplicate_type_name repr_name))
    | x -> Queue.enqueue let_toplevels x);
  process_types ~state type_defs;
  Queue.iter let_toplevels ~f:(function
    | `Let_fn (name, vars, expr) ->
      let expr = expand_expr ~counter:state.var_counter expr in
      let var_decls =
        List.map vars ~f:(function
          | `Typed (s, e) -> s, mono_of_type_expr ~state e
          | `Untyped s ->
            s, make_var_mono (Counter.next_alphabetical state.ty_var_counter))
      in
      let edge =
        Var.create_func
          ~ty_var_counter:state.ty_var_counter
          ~name
          ~expr
          ~var_decls
      in
      find_references
        ~edge
        ~locals:(function_arg_set ~init:String.Set.empty vars)
        expr
    | `Let (pattern, expr) ->
      let vars = Stack.create () in
      breakup_patterns ~counter:state.var_counter ~vars pattern expr;
      Stack.iter vars ~f:(fun (name, expr) ->
        let edge =
          Var.create_non_func ~ty_var_counter:state.ty_var_counter ~name ~expr
        in
        find_references ~edge ~locals:String.Set.empty expr)
    | `Extern (name, t, extern_name) ->
      let mono = mono_of_type_expr ~state t in
      let edge = Var.Extern (name, extern_name, mono) in
      (match Hashtbl.add state.glob_vars ~key:name ~data:edge with
       | `Ok -> ()
       | _ -> raise (Duplicate_type_name name))
    | `Implicit_extern (name, t, extern_name) ->
      let mono = mono_of_type_expr ~state t in
      let edge = Var.Implicit_extern (name, extern_name, mono) in
      (match Hashtbl.add state.glob_vars ~key:name ~data:edge with
       | `Ok -> ()
       | _ -> raise (Duplicate_type_name name))
    | _ -> failwith "impossible");
  match Hash_set.is_empty not_found_vars with
  | false ->
    raise
      (Unbound_var
         (Hash_set.find ~f:(Fn.const true) not_found_vars |> Option.value_exn))
  | true -> state
;;

let get_sccs glob_vars =
  let open Var in
  let res = Stack.create () in
  let stack = Stack.create () in
  let index = ref 0 in
  let rec connect v =
    v.scc_st.index <- Some !index;
    v.scc_st.lowlink <- !index;
    incr index;
    Stack.push stack v;
    v.scc_st.on_stack <- true;
    Set.iter v.used_globals ~f:(fun s ->
      let w = Hashtbl.find_exn glob_vars s in
      match w with
      | Extern _ | Implicit_extern _ -> ()
      | El w ->
        if Option.is_none w.scc_st.index
        then (
          connect w;
          v.scc_st.lowlink <- Int.min v.scc_st.lowlink w.scc_st.lowlink)
        else if w.scc_st.on_stack
        then
          v.scc_st.lowlink
          <- Int.min v.scc_st.lowlink (Option.value_exn w.scc_st.index));
    if v.scc_st.lowlink = Option.value_exn v.scc_st.index
    then (
      let scc = Stack.create () in
      let rec loop () =
        let w = Stack.pop_exn stack in
        w.scc_st.on_stack <- false;
        Stack.push scc w;
        match phys_equal v w with
        | true -> ()
        | false -> loop ()
      in
      loop ();
      Stack.push res scc)
  in
  Hashtbl.iter glob_vars ~f:(function
    | Extern _ | Implicit_extern _ -> ()
    | El v ->
      (match v.scc_st.index with
       | None -> connect v
       | Some _ -> ()));
  Stack.iter res ~f:(fun vars ->
    let scc = Var.{ vars; type_check_state = `Untouched } in
    Stack.iter vars ~f:(fun v -> v.Var.scc <- scc));
  res
;;

(* want to generalize sccs together *)

exception Early_exit

let rec unify a b =
  let fl sub a b =
    raise (Unification_error (Failed_to_match { failed = a, b; sub }))
  in
  try
    let a, b = inner_mono a, inner_mono b in
    if phys_equal a b then raise Early_exit;
    match a, b with
    | `Unit, `Unit | `I64, `I64 | `F64, `F64 | `Bool, `Bool | `Char, `Char -> a
    | `Pointer a, `Pointer b -> `Pointer (unify a b)
    | `Tuple l1, `Tuple l2 ->
      `Tuple (List.zip_exn l1 l2 |> List.map ~f:(fun (a, b) -> unify a b))
    | `Function (a, b), `Function (c, d) -> `Function (unify a c, unify b d)
    | `Var (_, r), o | o, `Var (_, r) | `Indir (_, r), o | o, `Indir (_, r) ->
      let m =
        match !r with
        | None -> o
        | Some m -> unify m o
      in
      r := Some m;
      m
    | `User a, `User b
      when String.equal (user_type a).repr_name (user_type b).repr_name ->
      let monos =
        List.zip_exn a.monos b.monos |> List.map ~f:(fun (a, b) -> unify a b)
      in
      `User { monos; user_type = a.user_type; inst_user_mono = None }
    | `User u, o | o, `User u ->
      (match user_type_monify u with
       | None -> raise (Unification_error End)
       | Some a -> unify a o)
    (* Opaque should only unify earlier with user_types exactly matching *)
    | `Opaque _, _ | _, `Opaque _ | _ -> raise (Unification_error End)
  with
  | Early_exit -> a
  | Unification_error sub -> fl sub a b
  | Invalid_argument _ -> fl End a b
;;

let poly_inner (poly : poly) =
  let rec go = function
    | `Mono mono -> mono
    | `For_all (_, r) -> go r
  in
  go poly
;;

let gen_helper ~vars ~indirs ~counter ~used mono : mono =
  let add mono' =
    match mono' with
    | `Var (s, _) ->
      if not (Hash_set.mem used s)
      then (
        Hash_set.add used s;
        Hashtbl.set vars ~key:s ~data:mono');
      mono'
    | _ -> mono'
  in
  let default () =
    let next_var = Counter.next_alphabetical counter in
    make_var_mono next_var
  in
  mono_map_rec_keep_refs mono ~f:(fun mono ->
    let mono' = inner_mono mono in
    match mono' with
    | `Var (x, _) -> Hashtbl.find_or_add vars x ~default |> add
    | `Indir (i, _) -> Hashtbl.find_or_add indirs i ~default |> add
    | _ -> mono')
;;

let make_weak_helper ~vars ~indirs mono : mono =
  mono_map_rec_keep_refs mono ~f:(fun mono ->
    let mono' = inner_mono mono in
    match mono' with
    | `Var (x, _) -> Hashtbl.find_or_add vars x ~default:make_indir
    | `Indir (i, _) -> Hashtbl.find_or_add indirs i ~default:make_indir
    | _ -> mono)
;;

let make_vars_weak ~vars ~indirs mono : poly =
  let mono =
    mono_map_rec_keep_refs
      ~f:(fun mono -> inner_mono mono |> make_weak_helper ~vars ~indirs)
      mono
  in
  `Mono mono
;;

let gen_mono ~counter ~vars ~indirs mono =
  let used = String.Hash_set.create () in
  inner_mono mono
  |> mono_map_rec_keep_refs ~f:(fun mono ->
    inner_mono mono |> gen_helper ~vars ~indirs ~counter ~used)
;;

let gen ~counter ~vars ~indirs mono =
  let used = String.Hash_set.create () in
  let mono =
    inner_mono mono
    |> mono_map_rec_keep_refs ~f:(fun mono ->
      inner_mono mono |> gen_helper ~vars ~indirs ~counter ~used)
  in
  Hash_set.fold used ~init:(`Mono mono) ~f:(fun acc key -> `For_all (key, acc))
;;

let gen_expr ~counter ~vars ~indirs (expr : Typed_ast.expr) : Typed_ast.gen_expr
  =
  let used = String.Hash_set.create () in
  let expr_inner, mono =
    Typed_ast.expr_map_monos expr ~f:(fun mono ->
      inner_mono mono |> gen_helper ~vars ~indirs ~counter ~used)
  in
  let poly =
    Hash_set.fold used ~init:(`Mono mono) ~f:(fun acc key ->
      `For_all (key, acc))
  in
  expr_inner, poly
;;

let make_vars_weak_expr ~vars ~indirs (expr : Typed_ast.expr)
  : Typed_ast.gen_expr
  =
  let expr_inner, mono =
    Typed_ast.expr_map_rec expr ~on_expr_inner:Fn.id ~on_mono:(fun mono ->
      inner_mono mono |> make_weak_helper ~vars ~indirs)
  in
  expr_inner, `Mono mono
;;

let state_add_local state ~name ~mono =
  { state with
    Type_state.locals = Map.set state.Type_state.locals ~key:name ~data:mono
  }
;;

let rec mono_of_var ~state name =
  match Map.find state.Type_state.locals name with
  | Some x -> `Local (x, String.Map.empty)
  | None ->
    (match Hashtbl.find state.Type_state.glob_vars name with
     | Some var -> infer_var ~state var
     | None -> raise (Unbound_var name))

and infer_var ~state var =
  match var with
  | Var.El v ->
    (match v.scc.type_check_state with
     | `Untouched -> infer_scc ~state v.Var.scc
     | `In_checking | `Done -> ());
    `Global (inst v.Var.poly)
  | Extern (_, _, mono) | Implicit_extern (_, _, mono) ->
    `Global (mono, String.Map.empty)

and infer_scc ~state scc =
  scc.Var.type_check_state <- `In_checking;
  let monos =
    Stack.to_list scc.Var.vars
    |> List.map ~f:(fun v ->
      let mono, _ = inst v.Var.poly in
      let state, to_unify, mono =
        match v.Var.args, mono with
        | `Func l, `Function (a, b) ->
          let tup =
            match l with
            | [ (_, m) ] -> m
            | _ -> `Tuple (List.map l ~f:snd)
          in
          let state =
            List.fold l ~init:state ~f:(fun state (key, data) ->
              { state with locals = Map.set state.locals ~key ~data })
          in
          let a = unify tup a in
          state, b, `Function (a, b)
        | _, _ -> state, mono, mono
      in
      let expr_inner, mono' = type_expr ~res_type:to_unify ~state v.Var.expr in
      v, (expr_inner, unify to_unify mono'), mono)
  in
  let counter = Counter.create () in
  let vars = String.Table.create () in
  let indirs = Int.Table.create () in
  List.iter monos ~f:(fun (v, expr, mono) ->
    let mono = mono_map_rec_keep_refs mono ~f:inner_mono in
    let expr, poly =
      match v.Var.args with
      | `Func l ->
        let expr = gen_expr ~counter ~vars ~indirs expr in
        let poly = gen ~counter ~vars ~indirs mono in
        let l =
          List.map l ~f:(fun (s, m) -> s, gen_mono ~counter ~vars ~indirs m)
        in
        v.Var.args <- `Func l;
        expr, poly
      | `Non_func ->
        let vars = String.Table.create () in
        let indirs = Int.Table.create () in
        ( make_vars_weak_expr ~vars ~indirs expr
        , make_vars_weak ~vars ~indirs mono )
    in
    v.Var.poly <- poly;
    v.Var.typed_expr <- Some expr);
  scc.Var.type_check_state <- `Done

and make_var ~state =
  make_var_mono (Counter.next_alphabetical state.Type_state.ty_var_counter)

and make_pointer ~state:_ =
  let ty_var = make_indir () in
  `Pointer ty_var, ty_var

and type_expr ~res_type ~state expr : Typed_ast.expr =
  let rep ~state = type_expr ~res_type ~state in
  match expr with
  | `Bool b -> `Bool b, `Bool
  | `Int i -> `Int i, `I64
  | `Null ->
    let pointer_type, _ = make_pointer ~state in
    `Null, pointer_type
  | `Return a ->
    let a, am = rep ~state a in
    let am = unify res_type am in
    `Return (a, am), `Unit
  | `Float f -> `Float f, `F64
  | `Char c -> `Char c, `Char
  | `String s -> `String s, `Pointer `Char
  | `Unit -> `Unit, `Unit
  | `Var name ->
    (match mono_of_var ~state name with
     | `Global (mono, inst_map) -> `Glob_var (name, inst_map), mono
     | `Local (mono, _) -> `Local_var name, mono)
  | `Array_lit l ->
    let init = make_indir () in
    let res_type, l' =
      List.fold_map ~init l ~f:(fun acc expr ->
        let expr' = rep ~state expr in
        unify acc (snd expr'), expr')
    in
    `Array_lit l', `Pointer res_type
  | `Tuple l ->
    let l' = List.map l ~f:(rep ~state) in
    let monos = List.map l' ~f:snd in
    `Tuple l', `Tuple monos
  | `Index (a, b) ->
    let a, am = rep ~state a in
    let b, bm = rep ~state b in
    let pointer_type, ty_var = make_pointer ~state in
    let am = unify am pointer_type in
    let bm = unify bm `I64 in
    `Index ((a, am), (b, bm)), ty_var
  | `Tuple_access (a, i) ->
    let a, am = rep ~state a in
    let res_type =
      match am with
      | `Tuple l ->
        (match List.nth l i with
         | Some x -> x
         | None -> failwith "Tuple access out of bounds")
      | _ -> failwith "must specify tuple type exactly if indexing"
    in
    `Tuple_access ((a, am), i), res_type
  | `Assign (a, b) ->
    let a, am = rep ~state a in
    let b, bm = rep ~state b in
    let bm = unify bm am in
    `Assign ((a, bm), (b, bm)), bm
  | `Assert_struct (str, a) ->
    let a, am = rep ~state a in
    let user_type = lookup_user_type ~state str in
    let user_type = inst_user_type_gen user_type in
    let am = unify am (`User user_type) in
    a, am
  | `Access_enum_field (field, a) ->
    let a, am = rep ~state a in
    let user_type' =
      match Hashtbl.find state.Type_state.variant_to_type field with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{field}`|}]
    in
    let inst_user_type = inst_user_type_gen user_type' in
    let res_type =
      get_user_type_variant (user_type inst_user_type) field
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
    in
    let am = unify am (`User inst_user_type) in
    `Access_enum_field (field, (a, am)), res_type
  | `Assert_empty_enum_field (field, a) ->
    let a, am = rep ~state a in
    let user_type' =
      match Hashtbl.find state.Type_state.variant_to_type field with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{field}`|}]
    in
    let inst_user_type = inst_user_type_gen user_type' in
    let res_type =
      get_user_type_variant (user_type inst_user_type) field
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
    in
    if Option.is_some res_type then raise (Unification_error End);
    let am = unify am (`User inst_user_type) in
    a, am
  | `Compound e ->
    let expr = rep ~state e in
    `Compound expr, snd expr
  | `Inf_op (op, a, b) ->
    let a, am = rep ~state a in
    let b, bm = rep ~state b in
    let m = unify am bm in
    let res_type =
      match op with
      | `Add | `Sub | `Mul | `Div | `Rem -> unify m `I64
      | `Eq | `Ne | `Lt | `Gt | `Le | `Ge -> `Bool
      | `And | `Or -> unify m `Bool
    in
    `Inf_op (op, (a, am), (b, bm)), res_type
  | `Field_access (a, field) ->
    let a, am = rep ~state a in
    let user_type =
      match Hashtbl.find state.Type_state.field_to_type field with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{field}`|}]
    in
    let user_type = inst_user_type_gen user_type in
    let res_type =
      get_user_type_field (get_user_type user_type) field
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
    in
    let am = unify am (`User user_type) in
    `Field_access ((a, am), field), res_type
  | `Ref a ->
    let a, am = rep ~state a in
    let pointer_type, ty_var = make_pointer ~state in
    let am = unify am ty_var in
    `Ref (a, am), pointer_type
  | `Deref a ->
    let a, am = rep ~state a in
    let pointer_type, ty_var = make_pointer ~state in
    let am = unify am pointer_type in
    `Deref (a, am), ty_var
  | `Pref_op (op, a) ->
    let a, am = rep ~state a in
    let res_type =
      match op with
      | `Minus -> unify am `I64
    in
    `Pref_op (op, (a, am)), res_type
  | `Struct (s, l) ->
    let user_type = lookup_user_type ~state s in
    let user_type = inst_user_type_gen user_type in
    let l = List.sort l ~compare:(fun (a, _) (b, _) -> String.compare a b) in
    let struct_l =
      (match !((get_user_type user_type).info) with
       | Some (`Struct l) -> l
       | _ -> raise (Unification_error End))
      |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
    in
    let l' =
      match List.zip struct_l l with
      | Ok l -> l
      | _ -> raise (Unification_error End)
    in
    let l' =
      List.map l' ~f:(fun ((orig_field, orig_mono), (field, opt_expr)) ->
        if not (String.equal orig_field field)
        then raise (Unification_error End);
        let expr =
          match opt_expr with
          | Some expr -> expr
          | None -> `Var field
        in
        let a, am = rep ~state expr in
        let am = unify am orig_mono in
        field, (a, am))
    in
    `Struct (s, l'), `User user_type
  | `Apply (`Enum s, e) ->
    let user_type =
      match Hashtbl.find state.Type_state.variant_to_type s with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{s}`|}]
    in
    let user_type = inst_user_type_gen user_type in
    let e, em = rep ~state e in
    let arg_type =
      get_user_type_variant (get_user_type user_type) s
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
    in
    let em = unify em arg_type in
    `Enum (s, Some (e, em)), `User user_type
  | `Enum s ->
    let user_type =
      match Hashtbl.find state.Type_state.variant_to_type s with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{s}`|}]
    in
    let user_type = inst_user_type_gen user_type in
    let arg_type =
      get_user_type_variant (get_user_type user_type) s
      |> Option.value_or_thunk ~default:(fun () ->
        raise (Unification_error End))
    in
    if Option.is_some arg_type then raise (Unification_error End);
    `Enum (s, None), `User user_type
  | `Apply (a, b) ->
    let a, am = rep ~state a in
    let b, bm = rep ~state b in
    let arg_type = make_indir () in
    let res_type = make_indir () in
    let func_type = `Function (arg_type, res_type) in
    let am = unify am func_type in
    let bm = unify bm arg_type in
    `Apply ((a, am), (b, bm)), res_type
  | `Typed (a, b) ->
    let a, am = rep ~state a in
    let b = mono_of_type_expr ~state b in
    let am = unify am b in
    a, am
  | `Let (s, b, c) ->
    let b, bm = rep ~state b in
    let state = state_add_local state ~name:s ~mono:bm in
    let c, cm = rep ~state c in
    `Let (s, (b, bm), (c, cm)), cm
  | `If (a, b, c) ->
    let a, am = rep ~state a in
    let b, bm = rep ~state b in
    let c, cm = rep ~state c in
    let am = unify am `Bool in
    let bm = unify bm cm in
    `If ((a, am), (b, bm), (c, cm)), bm
  | `Size_of (`Type t) ->
    let mono = mono_of_type_expr ~state t in
    `Size_of mono, `I64
  | `Size_of (`Expr e) ->
    let _, mono = rep ~state e in
    `Size_of mono, `I64
  | `Unsafe_cast e ->
    let expr = rep ~state e in
    let res_type = make_indir () in
    `Unsafe_cast expr, res_type
  | `Match (e, l) ->
    let initial_expr, em = rep ~state e in
    let res_type = make_indir () in
    let var = unique_name state.var_counter in
    let bound_expr = `Local_var var, em in
    let l =
      List.map l ~f:(fun (p, e) ->
        let conds, bindings_f, state =
          breakup_and_type_pattern ~state ~expr:bound_expr p
        in
        let e, em = rep ~state e in
        let em = unify em res_type in
        conds, bindings_f (e, em))
    in
    let _, (_, res_mono) = List.hd_exn l in
    let init = `Assert (`Bool false, `Bool), res_mono in
    let rest =
      List.fold_right
        ~init
        ~f:(fun (conds, (e, em)) acc -> `If (conds, (e, em), acc), em)
        l
    in
    `Let (var, (initial_expr, em), rest), res_mono

and breakup_and_type_pattern ~state ~expr:(e, em) pattern =
  let true_cond = `Bool true, `Bool in
  match pattern with
  | `Tuple l ->
    let l = List.map l ~f:(fun a -> a, make_indir ()) in
    let tuple_type = `Tuple (List.map l ~f:snd) in
    let em = unify em tuple_type in
    let expr = e, em in
    let conds = true_cond in
    let bindings_f expr = expr in
    List.foldi
      l
      ~init:(conds, bindings_f, state)
      ~f:(fun i (conds, bindings_f, state) (p, mono) ->
        let expr = `Tuple_access (expr, i), mono in
        let conds', bindings_f', state =
          breakup_and_type_pattern ~state ~expr p
        in
        let conds = Typed_ast.(conds && conds') in
        let bindings_f expr = bindings_f (bindings_f' expr) in
        conds, bindings_f, state)
  | `Var s ->
    let locals = Map.set state.locals ~key:s ~data:em in
    ( true_cond
    , (fun (e', em') -> `Let (s, (e, em), (e', em')), em')
    , { state with locals } )
  | `Bool b ->
    let _ = unify em `Bool in
    let conds = `Inf_op (`Eq, (e, em), (`Bool b, `Bool)), `Bool in
    conds, (fun expr -> expr), state
  | `Float f ->
    let _ = unify em `F64 in
    let conds = `Inf_op (`Eq, (e, em), (`Float f, `F64)), `Bool in
    conds, (fun expr -> expr), state
  | `Unit -> true_cond, (fun expr -> expr), state
  | `Ref p ->
    let pointer_type, ty_var = make_pointer ~state in
    let em = unify em pointer_type in
    let expr = `Deref (e, em), ty_var in
    breakup_and_type_pattern ~state ~expr p
  | `Char c ->
    let _ = unify em `Char in
    let conds = `Inf_op (`Eq, (e, em), (`Char c, `Char)), `Bool in
    conds, (fun expr -> expr), state
  | `String s ->
    let _ = unify em (`Pointer `Char) in
    let conds = `Inf_op (`Eq, (e, em), (`String s, `Pointer `Char)), `Bool in
    conds, (fun expr -> expr), state
  | `Int i ->
    let _ = unify em `I64 in
    let conds = `Inf_op (`Eq, (e, em), (`Int i, `I64)), `Bool in
    conds, (fun expr -> expr), state
  | `Null ->
    let pointer_type, _ = make_pointer ~state in
    let _ = unify em pointer_type in
    let conds = `Inf_op (`Eq, (e, em), (`Null, pointer_type)), `Bool in
    conds, (fun expr -> expr), state
  | `Typed (a, b) ->
    let b = mono_of_type_expr ~state b in
    let em = unify em b in
    breakup_and_type_pattern ~state ~expr:(e, em) a
  | `Struct (name, l) ->
    let user_type = lookup_user_type ~state name in
    let user_type = inst_user_type_gen user_type in
    let em = unify em (`User user_type) in
    let expr = e, em in
    let conds = true_cond in
    let bindings_f expr = expr in
    let struct_l =
      (match !((get_user_type user_type).info) with
       | Some (`Struct l) -> l
       | _ -> raise (Unification_error End))
      |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
    in
    let l' =
      match List.zip struct_l l with
      | Ok l -> l
      | _ -> failwith [%string {| Wrong number of fields in struct `%{name}`|}]
    in
    List.fold
      l'
      ~init:(conds, bindings_f, state)
      ~f:
        (fun
          (conds, bindings_f, state)
          ((orig_field, orig_mono), (field, opt_pattern))
        ->
        if not (String.equal orig_field field)
        then
          failwith
            [%string
              {| Wrong field name in struct `%{name}` (%{field} vs %{orig_field})|}];
        let pattern =
          match opt_pattern with
          | Some p -> p
          | None -> `Var field
        in
        let expr = `Field_access (expr, field), orig_mono in
        let conds', bindings_f', state =
          breakup_and_type_pattern ~state ~expr pattern
        in
        let conds = Typed_ast.(conds && conds') in
        let bindings_f expr = bindings_f (bindings_f' expr) in
        conds, bindings_f, state)
  | `Enum (name, opt_p) ->
    let user_type =
      match Hashtbl.find state.Type_state.variant_to_type name with
      | Some t -> t
      | None -> failwith [%string {| Unknown field `%{name}`|}]
    in
    let user_type = inst_user_type_gen user_type in
    let arg_type =
      get_user_type_variant (get_user_type user_type) name
      |> Option.value_or_thunk ~default:(fun () -> failwith "impossible")
    in
    let em = unify em (`User user_type) in
    let conds = `Check_variant (name, (e, em)), `Bool in
    (match opt_p with
     | Some p ->
       let arg_type =
         Option.value_or_thunk arg_type ~default:(fun () ->
           failwith [%string "variant does not have data `%{name}`"])
       in
       let expr = `Access_enum_field (name, (e, em)), arg_type in
       let conds', binding_f, state = breakup_and_type_pattern ~state ~expr p in
       let conds = Typed_ast.(conds && conds') in
       conds, binding_f, state
     | None ->
       if Option.is_some arg_type
       then failwith [%string "variant has data `%{name}`"];
       conds, (fun expr -> expr), state)
;;

type output =
  { glob_vars : Var.t String.Table.t
  ; types : user_type String.Table.t
  ; var_counter : Counter.t
  }

let type_check toplevels =
  try
    let state = process_toplevel_graph toplevels in
    (*
       Hashtbl.iter state.glob_vars ~f:(fun var ->
       match var with
       | Var.El v -> print_s [%sexp (v.Var.expr : expanded_expr)]
       | _ -> ());
    *)
    let _ = get_sccs state.glob_vars in
    Hashtbl.iter state.glob_vars ~f:(fun var -> ignore (infer_var ~state var));
    { glob_vars = state.glob_vars
    ; types = state.types
    ; var_counter = state.var_counter
    }
  with
  | Unification_error e ->
    show_unification_error e |> print_endline;
    exit 1
;;

let process_and_dump toplevels =
  let output = type_check toplevels in
  Hashtbl.iter output.glob_vars ~f:(fun var ->
    match var with
    | Var.El { typed_expr = Some e; name; poly; _ } ->
      print_endline [%string "Inferred %{name} to have type %{show_poly poly}"];
      print_s [%sexp (e : Typed_ast.gen_expr)]
    | _ -> ())
;;
