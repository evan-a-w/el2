open! Core
open! Ast
open! Types
open! Type_check

(* defaulting to unit is necessary here because
   bottom types end up just being a ty var.
   this happens for 'return'.
   TODO?: make an actual bottom type *)

(* FIXME: make variable shadowing work! important!
   currently generates incorrect code when a shadowed variable is created with an
   expression including the variable it shadows, eg.
   [ let f(s) := let s = 1 + s in s ]
   also it sometimes will have compiler errors because C doesn't (?) allow shadowing
   in the same scope (?) *)
let reach_end = Typed_ast.reach_end ~default:`Unit

exception Invalid_type of mono
exception Invalid_user_type of inst_user_type

let tuple_repr_name = "1tuple"

module Inst_map = Map.Make (struct
    type t = mono String.Map.t [@@deriving sexp, compare]
  end)

type var =
  { name : string
  ; gen_expr : gen_expr
  ; mutable cache : string Inst_map.t
  }

module Mono_list_map = Map.Make (struct
    type t = mono list [@@deriving sexp, compare]
  end)

type type_cache = string Mono_list_map.t ref

type type_def_edge =
  { strong_edges : type_def_edge Queue.t
  ; weak_edges : type_def_edge Queue.t
  ; monos : mono list
  ; repr_name : string
  ; mutable edge_def_buf : Bigbuffer.t option
  ; mutable visited : bool
  }

type type_def_state =
  { parent : ([ `Weak | `Strong ] * type_def_edge) option
  ; curr_def : Bigbuffer.t
  ; new_edges : type_def_edge Queue.t
  }

type state =
  { input : Type_state.t
  ; tree_walk_state : Tree_walk.state
  ; extern_vars : string String.Table.t
  ; vars : var String.Table.t
  ; inst_user_types : type_cache String.Table.t
  ; inst_monos : string Mono_map.t ref
  ; type_decl_buf : Bigbuffer.t
  ; type_buf : Bigbuffer.t
  ; decl_buf : Bigbuffer.t
  ; def_buf : Bigbuffer.t
  ; var_counter : Counter.t
  ; loop_value_name : string option
  ; comptime_eval : bool
  ; repr_name_to_edge : type_def_edge Mono_list_map.t ref String.Table.t
  }

type c_type_error =
  | End
  | Error_in of mono * c_type_error

let show_c_type_error err =
  let buf = Buffer.create 100 in
  let rec helper = function
    | End -> Buffer.add_string buf "end"
    | Error_in (m, e) ->
      Buffer.add_string buf (show_mono m);
      Buffer.add_string buf " because ";
      helper e
  in
  Buffer.add_string buf "error in ";
  helper err;
  Buffer.contents buf
;;

exception C_type_error of c_type_error

let make_weak type_def_state =
  match type_def_state.parent with
  | Some (_, e) -> { type_def_state with parent = Some (`Weak, e) }
  | None -> type_def_state
;;

let lookup_edge_map ~state repr_name =
  match Hashtbl.find state.repr_name_to_edge repr_name with
  | Some x -> x
  | None ->
    let data = ref Mono_list_map.empty in
    Hashtbl.set state.repr_name_to_edge ~key:repr_name ~data;
    data
;;

let lookup_edge ~type_def_state ~state repr_name monos =
  let map = lookup_edge_map ~state repr_name in
  match Map.find !map monos with
  | Some x -> x
  | None ->
    let edge =
      { strong_edges = Queue.create ()
      ; weak_edges = Queue.create ()
      ; monos
      ; repr_name
      ; edge_def_buf = Some (Bigbuffer.create 100)
      ; visited = false
      }
    in
    Queue.enqueue type_def_state.new_edges edge;
    map := Map.set !map ~key:monos ~data:edge;
    edge
;;

let add_edge ~type_def_state ~state repr_name monos =
  let edge = lookup_edge ~type_def_state ~state repr_name monos in
  ( edge
  , { type_def_state with
      parent = Some (`Strong, edge)
    ; curr_def = Option.value edge.edge_def_buf ~default:type_def_state.curr_def
    } )
;;

let rec c_type_of_user_type' ~type_def_state ~state inst =
  let user_type =
    get_insted_user_type inst
    |> Option.value_or_thunk ~default:(fun () -> raise (Invalid_user_type inst))
  in
  let map_ref =
    Hashtbl.find_or_add
      state.inst_user_types
      user_type.repr_name
      ~default:(fun () -> ref Mono_list_map.empty)
  in
  let monos = List.map inst.monos ~f:reach_end in
  let parent = type_def_state.parent in
  let edge, type_def_state =
    add_edge ~state ~type_def_state user_type.repr_name monos
  in
  (match parent with
   | None -> ()
   | Some (`Strong, e) -> Queue.enqueue e.strong_edges edge
   | Some (`Weak, e) -> Queue.enqueue e.weak_edges edge);
  match Map.find !map_ref monos, !(user_type.info) with
  | Some x, _ -> x
  | None, None -> raise (Invalid_user_type inst)
  | None, Some (`Alias m) ->
    let name = string_of_mono (`User inst) in
    let data = "alias_" ^ name in
    map_ref := Map.set !map_ref ~key:monos ~data;
    let res = c_type_of_mono' ~type_def_state ~state m in
    Bigbuffer.add_string
      state.type_decl_buf
      [%string {|typedef %{res} %{data};|}];
    res
  | None, Some ((`Struct _ | `Enum _) as i) ->
    let name = string_of_mono (`User inst) in
    let data = "struct " ^ name in
    Bigbuffer.add_string state.type_decl_buf [%string {|%{data};|}];
    map_ref := Map.set !map_ref ~key:monos ~data;
    (match i with
     | `Struct l ->
       define_struct ~type_def_state ~state ~name ~l;
       data
     | `Enum l ->
       define_enum ~type_def_state ~state ~name ~l;
       data)

and c_type_of_function ~type_def_state ~state mono (a, b) =
  match Map.find !(state.inst_monos) mono with
  | Some x -> x
  | None ->
    let name = string_of_mono mono in
    state.inst_monos := Map.set !(state.inst_monos) ~key:mono ~data:name;
    let args =
      match a with
      | `Tuple l -> l
      | _ -> [ a ]
    in
    Bigbuffer.add_string
      type_def_state.curr_def
      (function_typedef_string ~type_def_state ~state ~name ~args ~ret:b);
    name

and c_type_of_tuple ~type_def_state ~state l =
  let l = List.map l ~f:reach_end in
  let mono = `Tuple l in
  let parent = type_def_state.parent in
  let edge, type_def_state =
    add_edge ~state ~type_def_state tuple_repr_name l
  in
  (match parent with
   | None -> ()
   | Some (`Strong, e) -> Queue.enqueue e.strong_edges edge
   | Some (`Weak, e) -> Queue.enqueue e.weak_edges edge);
  match Map.find !(state.inst_monos) mono with
  | Some x -> x
  | None ->
    let mono_name = string_of_mono mono in
    let name = "struct " ^ mono_name in
    Bigbuffer.add_string state.type_decl_buf [%string {|%{name};|}];
    state.inst_monos := Map.set !(state.inst_monos) ~key:mono ~data:name;
    let fields =
      List.mapi l ~f:(fun i x ->
        let a = [%string {| %{mono_name}_%{i#Int} |}] in
        let b = c_type_of_mono' ~type_def_state ~state x in
        [%string {|%{b} %{a};|}])
      |> String.concat ~sep:"\n"
    in
    Bigbuffer.add_string
      type_def_state.curr_def
      [%string {|%{name} {%{fields}};|}];
    name

and c_type_of_mono' ~type_def_state ~state (mono : mono) =
  try
    let mono = reach_end mono in
    match mono with
    | `Bottom -> assert false
    | `Bool -> "bool"
    | `I64 -> "int64_t"
    | `C_int -> "int"
    | `F64 -> "double"
    | `Unit -> "void"
    | `Char -> "char"
    | `User x -> c_type_of_user_type' ~type_def_state ~state x
    | `Opaque x -> c_type_of_mono' ~type_def_state ~state x
    | `Pointer x ->
      let type_def_state = make_weak type_def_state in
      let x = c_type_of_mono' ~type_def_state ~state x in
      x ^ "*"
    | `Function (a, b) -> c_type_of_function ~type_def_state ~state mono (a, b)
    | `Tuple l -> c_type_of_tuple ~type_def_state ~state l
    | `Indir _ | `Var _ -> raise (Invalid_type mono)
  with
  | Typed_ast.Incomplete_type m -> raise (C_type_error (Error_in (m, End)))
  | C_type_error e -> raise (C_type_error (Error_in (mono, e)))

and function_typedef_string ~type_def_state ~state ~name ~args ~ret =
  let args =
    List.filter_map args ~f:(fun mono ->
      match mono with
      | `Unit -> None
      | _ -> Some (c_type_of_mono' ~type_def_state ~state mono))
    |> String.concat ~sep:", "
  in
  let ret = c_type_of_mono' ~type_def_state ~state ret in
  [%string {|typedef %{ret} (*%{name})(%{args});|}]

and define_struct ~type_def_state ~state ~name ~l =
  let l =
    List.map l ~f:(fun (a, b) ->
      match reach_end b with
      | `Unit -> ""
      | _ ->
        let b = c_type_of_mono' ~type_def_state ~state b in
        [%string {|%{b} %{a};|}])
    |> String.concat ~sep:"\n"
  in
  Bigbuffer.add_string
    type_def_state.curr_def
    [%string {|struct %{name} {%{l}};|}]

and enum_tag ~name ~variant =
  String.uppercase name ^ "_" ^ String.uppercase variant ^ "_TAG"

and define_enum ~type_def_state ~state ~name ~l =
  let tags =
    List.map l ~f:(fun (a, _) -> enum_tag ~name ~variant:a)
    |> String.concat ~sep:", "
  in
  (* first define the enum *)
  let enum_name = [%string "enum %{name}_tag"] in
  Bigbuffer.add_string
    type_def_state.curr_def
    [%string {| %{enum_name} {%{tags}}; |}];
  let union_inside =
    List.filter_map l ~f:(fun (a, b) ->
      match b with
      | None -> None
      | Some b ->
        (match reach_end b with
         | `Unit -> None
         | _ ->
           let b = c_type_of_mono' ~type_def_state ~state b in
           Some [%string {|%{b} %{a};|}]))
    |> String.concat ~sep:"\n"
  in
  Bigbuffer.add_string
    type_def_state.curr_def
    [%string
      {| struct %{name} {
           %{enum_name} tag;
           union {
               %{union_inside}
           } data;
         };
      |}]
;;

let do_c_type_of ~f ~state arg =
  let curr_def = Bigbuffer.create 100 in
  let type_def_state =
    { new_edges = Queue.create (); parent = None; curr_def }
  in
  let res = f ~type_def_state ~state arg in
  let add_def edge =
    match edge.edge_def_buf with
    | Some buf ->
      Bigbuffer.add_buffer state.type_buf buf;
      edge.edge_def_buf <- None
    | None -> ()
  in
  let rec helper edge =
    if not edge.visited
    then (
      edge.visited <- true;
      Queue.iter edge.strong_edges ~f:helper;
      add_def edge)
  in
  Queue.iter type_def_state.new_edges ~f:helper;
  Bigbuffer.add_buffer state.type_buf curr_def;
  Queue.iter type_def_state.new_edges ~f:add_def;
  res
;;

let c_type_of_mono ~state mono = do_c_type_of ~f:c_type_of_mono' ~state mono

let c_type_of_user_type ~state inst =
  do_c_type_of ~f:c_type_of_user_type' ~state inst
;;

let declare_function ~state ~name ~args ~ret =
  let args =
    List.filter_map args ~f:(fun (_, mono) ->
      match mono with
      | `Unit -> None
      | _ -> Some (c_type_of_mono ~state mono))
    |> String.concat ~sep:", "
  in
  let ret = c_type_of_mono ~state ret in
  Bigbuffer.add_string state.decl_buf [%string {|%{ret} %{name}(%{args});|}]
;;

let declare_extern ~state ~name ~mono =
  let mono = reach_end mono in
  match mono with
  | `Unit -> ()
  | _ ->
    let c_type = c_type_of_mono ~state mono in
    Bigbuffer.add_string state.decl_buf [%string {|extern %{c_type} %{name};|}]
;;

let rec var_to_string_inner ~state ~inst_map (var : Type_check.var) =
  let gen_expr =
    match var.typed_expr with
    | None -> failwith "untyped var!"
    | Some x -> x
  in
  let comp_var =
    Hashtbl.find_or_add state.vars var.unique_name ~default:(fun () ->
      { name = var.unique_name; gen_expr; cache = Inst_map.empty })
  in
  let expr_inner, poly = gen_expr in
  let ((_, mono) as expr) =
    (expr_inner, poly_inner poly)
    |> Typed_ast.expr_map_rec
         ~on_expr_inner:Fn.id
         ~on_mono:(inst_mono ~inst_map)
  in
  try
    match Map.find comp_var.cache inst_map with
    | Some x -> x
    | None ->
      let suffix =
        Map.data inst_map
        |> List.map ~f:string_of_mono
        |> String.concat ~sep:"_"
      in
      let name =
        match Map.length inst_map with
        | 0 -> comp_var.name
        | _ -> comp_var.name ^ "_inst_" ^ suffix
      in
      comp_var.cache <- Map.set comp_var.cache ~key:inst_map ~data:name;
      (match var.args with
       | `Non_func ->
         (match mono with
          (* Since toplevels are comptime, we can skip unit ones (no side effects) *)
          | `Unit -> ""
          | _ ->
            let expr =
              match state.comptime_eval with
              | true -> Tree_walk.eval ~state:state.tree_walk_state ~var expr
              | false -> expr
            in
            define_toplevel_val_with_name ~state ~name expr;
            name)
       | `Func args ->
         let args = List.map args ~f:(fun (s, m) -> s, inst_mono ~inst_map m) in
         declare_function ~state ~name ~args ~ret:mono;
         define_func ~state ~name ~args ~ret:mono ~expr;
         name)
  with
  | C_type_error _ as exn ->
    print_var_comp_error var inst_map mono exn;
    exit 1
  | Invalid_user_type u as exn ->
    print_endline [%string "Invalid user type %{show_mono (`User u)}"];
    print_var_comp_error var inst_map mono exn;
    exit 1
  | Typed_ast.Incomplete_type m as exn ->
    print_endline "Incomplete type in var_to_string_inner";
    print_endline (show_mono m);
    let pretty_expr = Pretty_print.typed_ast expr |> Pretty_print.to_string in
    print_endline pretty_expr;
    print_var_comp_error var inst_map mono exn;
    exit 1

and print_exn_backtrace exn =
  Backtrace.Exn.most_recent_for_exn exn
  |> Option.value_exn
  |> Backtrace.to_string
  |> print_endline

and print_var_comp_error var inst_map mono exn =
  let inst_map =
    Map.to_alist inst_map
    |> List.map ~f:(fun (a, b) -> [%string {| %{a} = %{show_mono b} |}])
    |> String.concat ~sep:",\n"
  in
  print_endline
    [%string {| while compiling %{var.name} with type %{show_mono mono} |}];
  print_endline [%string {| with inst_map `%{inst_map}` |}];
  print_exn_backtrace exn

and var_to_string ~state ~inst_map var =
  match var with
  | Typed_ast.El var -> var_to_string_inner ~state ~inst_map var
  | Implicit_extern (_, extern_name, _) -> extern_name
  | Extern (internal_name, extern_name, mono) ->
    (match mono with
     | `Unit -> ""
     | _ ->
       Hashtbl.find_or_add state.extern_vars internal_name ~default:(fun () ->
         declare_extern ~state ~name:extern_name ~mono;
         extern_name))

and define_func ~state ~name ~args ~ret ~expr =
  let buf = Bigbuffer.create 100 in
  function_definition ~state ~buf ~name ~args ~ret;
  Bigbuffer.add_string buf "{ ";
  let s = expr_to_string ~state ~buf ~expr in
  (match snd expr |> reach_end with
   | `Unit ->
     Bigbuffer.add_string buf s;
     Bigbuffer.add_char buf ';'
   | _ -> Bigbuffer.add_string buf [%string {| return %{s}; |}]);
  Bigbuffer.add_string buf " }";
  Bigbuffer.add_buffer state.def_buf buf

and function_definition ~state ~buf ~name ~args ~ret =
  let ret = c_type_of_mono ~state ret in
  let args =
    List.filter_map args ~f:(fun (a, b) ->
      match b with
      | `Unit -> None
      | _ -> Some [%string {|%{c_type_of_mono ~state b} %{a}|}])
    |> String.concat ~sep:", "
  in
  Bigbuffer.add_string buf [%string {|%{ret} %{name}(%{args})|}]

and declare_inner_val ~state ~buf ~name ~mono =
  let mono = reach_end mono in
  match name, mono with
  | "_", _ | _, `Unit -> ()
  | _ ->
    let c_type = c_type_of_mono ~state mono in
    Bigbuffer.add_string buf [%string {|%{c_type} %{name};|}]

and declare_val ~state ~name ~mono =
  declare_inner_val ~state ~buf:state.decl_buf ~name ~mono

and add_equal name =
  match name with
  | "" -> ""
  | _ -> name ^ " = "

and nameify name ~expr =
  match name, fst expr, snd expr |> reach_end with
  | _, `Compound expr, _ -> nameify name ~expr 
  | _, `Let (_, _, expr), _ -> nameify name ~expr
  | "_", _, _
  | _, _, (`Unit | `Bottom)
  | _, (`Assert (`Bool false, _) | `Return _), _ -> ""
  | _ -> name

and define_toplevel_val_with_name ~state ~name expr =
  let buf = state.def_buf in
  let type_str = c_type_of_mono ~state (snd expr) in
  let name = nameify name ~expr in
  let res = expr_to_string ~state ~buf ~expr in
  let res =
    nameify [%string {| %{type_str} %{add_equal name}%{res}; |}] ~expr
  in
  Bigbuffer.add_string buf res

and define_inner_val_with_name ~state ~buf ~name expr =
  let name = nameify name ~expr in
  let expr = expr_to_string ~state ~buf ~expr in
  Bigbuffer.add_string buf [%string {| %{add_equal name}%{expr}; |}];
  name

and create_inner_val_with_name ~state ~buf ~name expr =
  declare_inner_val ~state ~buf ~name ~mono:(snd expr);
  define_inner_val_with_name ~state ~buf ~name expr

and create_inner_val ~state ~buf expr =
  let name = Type_state.unique_name state.input in
  create_inner_val_with_name ~state ~buf ~name expr

and expr_to_string ~state ~buf ~expr:(expr_inner, mono) =
  try
    let get_typ_no_struct mono =
      let typ = c_type_of_mono ~state mono in
      typ, String.chop_prefix_if_exists ~prefix:"struct " typ
    in
    match expr_inner with
    | `Null -> "NULL"
    | `Bool true -> "true"
    | `Bool false -> "false"
    | `Size_of mono ->
      let typ = c_type_of_mono ~state mono in
      (match mono with
       | `Unit -> "0"
       | _ -> [%string {| sizeof(%{typ}) |}])
    | `Return x -> [%string {| return %{expr_to_string ~state ~buf ~expr:x}; |}]
    | `Array_lit l ->
      let inners =
        List.map l ~f:(fun expr -> expr_to_string ~state ~buf ~expr)
        |> String.concat ~sep:","
      in
      let name = Type_state.unique_name state.input in
      let typ = c_type_of_mono ~state (List.hd_exn l |> snd) in
      Bigbuffer.add_string buf [%string {| %{typ} %{name}[] = { %{inners} }; |}];
      name
    | `Tuple l ->
      let _, typ_no_struct = get_typ_no_struct mono in
      let inners =
        List.map l ~f:(fun expr -> expr_to_string ~state ~buf ~expr)
        |> List.mapi ~f:(fun i s ->
          [%string {| .%{typ_no_struct}_%{i#Int} = %{s} |}])
        |> String.concat ~sep:", "
      in
      [%string "(%{c_type_of_mono ~state mono}){ %{inners} }"]
    | `Index (a, b) ->
      let a = expr_to_string ~state ~buf ~expr:a in
      let b = expr_to_string ~state ~buf ~expr:b in
      [%string {| (%{a})[%{b}] |}]
    | `Tuple_access ((a, am), i) ->
      let _, typ_no_struct = get_typ_no_struct am in
      let num =
        match am with
        | `Tuple l -> List.length l
        | _ -> 0
      in
      let a = expr_to_string ~state ~expr:(a, am) ~buf in
      (match i < num with
       | true -> [%string {| (%{a}).%{typ_no_struct}_%{i#Int} |}]
       | false -> failwith "tuple access out of bounds")
    | `Assign (a, b) ->
      let a = expr_to_lvalue_string ~state ~expr:a ~buf in
      let a = nameify a ~expr:b in
      let b = expr_to_string ~state ~expr:b ~buf in
      [%string {| %{add_equal a}%{b}; |}]
    | `Glob_var (var, inst_map) ->
      let inst_map =
        match var, inst_map with
        | _, Some x -> x
        | El var, None ->
          (match var.poly with
           | `Mono _ -> String.Map.empty
           | _ ->
             let inst_map' =
               recover_inst_map (poly_inner var.poly) mono String.Map.empty
             in
             inst_map')
        | _ -> String.Map.empty
      in
      var_to_string ~state ~inst_map var
    | `Local_var name ->
      (match reach_end mono with
       | `Unit -> ""
       | _ -> name)
    | `Access_enum_field (field, expr) ->
      (match reach_end mono with
       | `Unit -> define_inner_val_with_name ~state ~buf ~name:"_" expr
       | _ ->
         [%string {| (%{expr_to_string ~state ~expr ~buf}).data.%{field} |}])
    | `Compound e ->
      let res_val = unique_name_or_empty ~state ~buf ~mono in
      let res_val = nameify res_val ~expr:e in
      Bigbuffer.add_char buf '{';
      let res = expr_to_string ~state ~expr:e ~buf in
      Bigbuffer.add_string buf [%string {| %{add_equal res_val} |}];
      Bigbuffer.add_string buf res;
      Bigbuffer.add_char buf ';';
      Bigbuffer.add_char buf '}';
      res_val
    | `Inf_op (`Eq, ((_, `Pointer `Char) as a), b) ->
      let a = expr_to_string ~buf ~state ~expr:a in
      let b = expr_to_string ~buf ~state ~expr:b in
      [%string {| (strcmp(%{a}, %{b}) == 0) |}]
    | `Inf_op (op, a, b) ->
      let a = expr_to_string ~buf ~state ~expr:a in
      let b = expr_to_string ~buf ~state ~expr:b in
      let op =
        match op with
        | `Ge -> ">="
        | `Rem -> "%"
        | `Div -> "/"
        | `Add -> "+"
        | `Lt -> "<"
        | `And -> "&&"
        | `Sub -> "-"
        | `Eq -> "=="
        | `Le -> "<="
        | `Or -> "||"
        | `Gt -> ">"
        | `Mul -> "*"
        | `Ne -> "!="
      in
      [%string {| ((%{a}) %{op} (%{b})) |}]
    | `Field_access (expr, field) ->
      (match reach_end mono with
       | `Unit -> define_inner_val_with_name ~state ~buf ~name:"_" expr
       | _ -> [%string {| (%{expr_to_string ~state ~expr ~buf}).%{field} |}])
    | `Float x -> Float.to_string x
    | `Unit -> ""
    | `Ref expr ->
      let expr = expr_to_lvalue_string ~state ~buf ~expr in
      (match expr with
       | "" -> "NULL"
       | _ -> [%string "&(%{expr})"])
    | `Deref e -> [%string "(*(%{expr_to_string ~state ~buf ~expr:e }))"]
    | `Char x -> [%string "'%{x}"]
    | `String s -> [%string {| "%{s}" |}]
    | `Int i -> [%string {| %{i#Int} |}]
    | `Check_variant (variant, expr) ->
      let _, typ_no_struct = get_typ_no_struct (snd expr) in
      let variant = enum_tag ~name:typ_no_struct ~variant in
      [%string {| ((%{expr_to_string ~state ~expr  ~buf}).tag == %{variant}) |}]
    | `Pref_op (op, e) ->
      let e = expr_to_string ~state ~buf ~expr:e in
      let op =
        match op with
        | `Minus -> "-"
      in
      [%string {| %{op}(%{e}) |}]
    | `Enum (s, p) ->
      let typ, typ_no_struct = get_typ_no_struct mono in
      let variant = enum_tag ~name:typ_no_struct ~variant:s in
      let union =
        match p with
        | None -> ""
        | Some expr ->
          (match snd expr |> reach_end with
           | `Unit -> ""
           | _ ->
             let var = expr_to_string ~state ~buf ~expr in
             [%string {| , .data = { .%{s} = %{var} } |}])
      in
      [%string {| (%{typ}){ .tag = %{variant}%{union} } |}]
    | `Struct fields ->
      let typ, _ = get_typ_no_struct mono in
      let fields =
        List.map fields ~f:(fun (s, expr) ->
          let expr = expr_to_string ~state ~buf ~expr in
          [%string {| .%{s} = %{expr} |}])
        |> String.concat ~sep:", "
      in
      [%string {| (%{typ}){ %{fields} } |}]
    | `Apply (a, ((be, _) as b)) ->
      let args =
        match be with
        | `Tuple l ->
          List.filter_map l ~f:(fun expr ->
            match expr_to_string ~state ~buf ~expr with
            | "" -> None
            | s -> Some s)
        | _ -> [ expr_to_string ~state ~buf ~expr:b ]
      in
      let args = String.concat ~sep:", " args in
      let a = expr_to_string ~state ~buf ~expr:a in
      [%string {| (%{a})(%{args}) |}]
    | `Let (name, a, b) ->
      let (_ : string) = create_inner_val_with_name ~state ~buf ~name a in
      expr_to_string ~state ~buf ~expr:b
    | `Loop a ->
      let name = unique_name_or_empty ~state ~buf ~mono in
      Bigbuffer.add_string buf [%string {| while (true) { |}];
      let a =
        expr_to_string
          ~state:{ state with loop_value_name = Some name }
          ~buf
          ~expr:a
      in
      Bigbuffer.add_string buf a;
      Bigbuffer.add_string buf ";}";
      name
    | `Break expr ->
      (match state.loop_value_name with
       | None -> failwith "break outside of loop"
       | Some name ->
         let a = expr_to_string ~state ~buf ~expr in
         Bigbuffer.add_string buf [%string {| %{add_equal name}%{a}; break; |}];
         "")
    | `If (a, b, c) ->
      let name = unique_name_or_empty ~state ~buf ~mono:(snd b) in
      let b_name = nameify name ~expr:b in
      let c_name = nameify name ~expr:c in
      let a = expr_to_string ~state ~buf ~expr:a in
      Bigbuffer.add_string buf [%string {| if (%{a}) { |}];
      let b = expr_to_string ~state ~buf ~expr:b in
      Bigbuffer.add_string buf [%string {| %{add_equal b_name}%{b};} else { |}];
      let c = expr_to_string ~state ~buf ~expr:c in
      Bigbuffer.add_string buf [%string {| %{add_equal c_name}%{c};} |}];
      name
    | `Assert e -> [%string {| assert(%{expr_to_string ~state ~buf ~expr:e}) |}]
    | `Unsafe_cast e ->
      let a = expr_to_string ~state ~buf ~expr:e in
      let cast_to = c_type_of_mono ~state mono in
      [%string "(%{cast_to})%{a}"]
  with
  | C_type_error e as exn ->
    show_c_type_error e |> print_endline;
    let pretty_expr =
      Pretty_print.typed_ast (expr_inner, mono) |> Pretty_print.to_string
    in
    print_endline "Failed in expr to string:";
    print_endline pretty_expr;
    raise exn

and expr_to_lvalue_string ~state ~buf ~expr =
  match fst expr with
  | `Deref _
  | `Local_var _
  | `Glob_var _
  | `Field_access _
  | `Access_enum_field _
  | `Tuple_access _
  | `Index _ -> expr_to_string ~state ~buf ~expr
  | _ -> create_inner_val ~state ~buf expr

and unique_name_or_empty ~state ~buf ~mono =
  match reach_end mono with
  | `Unit -> ""
  | _ ->
    let name = Type_state.unique_name state.input in
    declare_inner_val ~state ~buf ~name ~mono;
    name
;;

let state_of_input ~comptime_eval input =
  { input
  ; comptime_eval
  ; repr_name_to_edge = String.Table.create ()
  ; tree_walk_state = Tree_walk.make_state input
  ; vars = String.Table.create ()
  ; extern_vars = String.Table.create ()
  ; inst_user_types = String.Table.create ()
  ; inst_monos = ref Mono_map.empty
  ; type_buf = Bigbuffer.create 100
  ; type_decl_buf = Bigbuffer.create 100
  ; decl_buf = Bigbuffer.create 100
  ; def_buf = Bigbuffer.create 100
  ; var_counter = input.var_counter
  ; loop_value_name = None
  }
;;

let headers =
  "#include <stdint.h>\n\
   #include <stdbool.h>\n\
   #include <stdlib.h>\n\
   #include <string.h>\n\
   #include <assert.h>\n\
   #include <stdio.h>\n\
   #include <sys/mman.h>\n"
;;

let rec compile_module ~state module_t =
  Hashtbl.iter module_t.Type_state.sub_modules ~f:(fun module_t ->
    compile_module ~state module_t);
  Hashtbl.iteri module_t.types ~f:(fun ~key:_ ~data ->
    match data.ty_vars with
    | [] ->
      let inst_user_type =
        { monos = []
        ; orig_user_type = data
        ; insted_user_type = ref (Some data)
        }
      in
      ignore (c_type_of_user_type ~state inst_user_type)
    | _ -> ());
  Hashtbl.iteri module_t.glob_vars ~f:(fun ~key:_ ~data ->
    (* inst all monomorphic thingos *)
    match data with
    | Typed_ast.El { poly = `Mono _; _ } | Extern _ ->
      ignore (var_to_string ~state ~inst_map:String.Map.empty data)
    | _ -> ())
;;

let compile ~for_header ~comptime_eval ~input ~chan =
  let state = state_of_input ~comptime_eval input in
  Hashtbl.iter input.seen_files ~f:(compile_module ~state);
  Out_channel.output_string chan headers;
  Bigbuffer.contents state.type_decl_buf |> Out_channel.output_string chan;
  Bigbuffer.contents state.type_buf |> Out_channel.output_string chan;
  Bigbuffer.contents state.decl_buf |> Out_channel.output_string chan;
  if not for_header
  then Bigbuffer.contents state.def_buf |> Out_channel.output_string chan
;;

let rec print_module input =
  Hashtbl.iter input.Type_state.sub_modules ~f:(fun input ->
    print_endline [%string "Submodule %{input.name}"];
    print_module input);
  Hashtbl.iter input.Type_state.glob_vars ~f:(fun var ->
    match var with
    | Typed_ast.El { poly; name; typed_expr; _ } ->
      let expr_inner, poly' = Option.value_exn typed_expr in
      let mono = poly_inner poly' in
      Pretty_print.print ~name ~poly ~typed_ast:(expr_inner, mono)
    | _ -> ())
;;

let print_typed_ast filename =
  let input, _ = Type_check.type_check_and_output filename in
  Hashtbl.iter input.seen_files ~f:print_module
;;

let transpile_fully ~for_header ~comptime_eval ~chan filename =
  let input, has_main = Type_check.type_check_and_output filename in
  compile ~for_header ~comptime_eval ~input ~chan;
  has_main
;;
