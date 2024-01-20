open! Core
open! Ast
open! Types
open Type_common

type unification_error =
  | Failed_to_match of
      { sub : unification_error
      ; failed : mono * mono
      }
  | End
[@@deriving sexp]

module type Iterable = sig
  type 'a t

  val iter : 'a t -> f:('a -> unit) -> unit
end

let rec show_unification_error = function
  | Failed_to_match { sub; failed = a, b } ->
    [%string
      {| Failed to match %{a |> show_mono} and %{b |> show_mono} because %{show_unification_error sub} |}]
  | End -> "End"
;;

let print_sccs = false

exception Unification_error of unification_error
exception Infinite_type of string

exception
  Module_cycle of
    { from_module : string
    ; offending_module : string
    }

exception Early_exit

let unel2_file filename =
  try
    let dir, name = Filename.split filename in
    let rex = Re.Pcre.regexp {|[a-z]([a-z0-9_]*)\.el2$|} in
    let group = Re.Pcre.exec ~rex name in
    let rest = Re.Group.get group 1 in
    let fst_char = name.[0] |> Char.uppercase in
    dir, [%string "%{fst_char#Char}%{rest}"]
  with
  | _ -> failwith [%string {|Invalid filename: `%{filename}`|}]
;;

let el2_file dir name =
  let fst_char = name.[0] |> Char.lowercase in
  let rest_chars = String.sub name ~pos:1 ~len:(String.length name - 1) in
  Filename.concat dir [%string "%{fst_char#Char}%{rest_chars}.el2"]
;;

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
      when String.equal a.orig_user_type.repr_name b.orig_user_type.repr_name ->
      let monos =
        List.zip_exn a.monos b.monos |> List.map ~f:(fun (a, b) -> unify a b)
      in
      `User { a with monos }
    | `User u, o | o, `User u ->
      (match user_type_monify u with
       | None -> raise (Unification_error End)
       | Some a -> unify a o)
    (* Opaque should only unify earlier with user_types exactly matching *)
    | `Opaque _, _ | _, `Opaque _ | _ -> raise (Unification_error End)
  with
  | Early_exit -> a
  | Unification_error sub -> fl sub a b
  (* this is just to catch exns from List.zip_exn *)
  | Invalid_argument _ -> fl End a b
;;

let inst_user_type_exn inst_user_type =
  get_insted_user_type inst_user_type
  |> Option.value_or_thunk ~default:(fun () -> failwith "Undefined type")
;;

let rec inner_info (info : all_user option) =
  match info with
  | Some (`Alias (`User u)) ->
    inner_info
      (get_insted_user_type u |> Option.bind ~f:(fun { info; _ } -> !info))
  | _ -> info
;;

let get_user_type_field user_type field =
  match inner_info !(user_type.info) with
  | Some (`Struct l) ->
    List.find l ~f:(fun (a, _) -> String.equal a field)
    |> Option.map ~f:Tuple2.get2
  | _ -> None
;;

let get_user_type_variant user_type variant =
  match inner_info !(user_type.info) with
  | Some (`Enum l) ->
    List.find l ~f:(fun (a, _) -> String.equal a variant)
    |> Option.map ~f:Tuple2.get2
  | _ -> None
;;

let rec last_user_type_info_not_insted (mono : mono) =
  match mono with
  | `User u ->
    (match !(u.orig_user_type.info) with
     | Some (`Alias m) -> last_user_type_info_not_insted m
     | o -> o)
  | _ -> Some (`Alias mono)
;;

let internal_var counter = "internal_" ^ Counter.next_num counter

module Type_state = struct
  module T = struct
    type module_name = string [@@deriving sexp, compare]

    module Module_name_set = Set.Make (struct
        type t = module_name [@@deriving sexp, compare]
      end)

    type module_t =
      { name : module_name
      ; dir : string
      ; sub_modules : module_t String.Table.t
      ; glob_vars : module_t list Typed_ast.top_var String.Table.t
      ; types : user_type String.Table.t
      ; variant_to_type : user_type String.Table.t
      ; field_to_type : user_type String.Table.t
      ; mutable in_eval : bool
      ; parent : module_t option
      }
    [@@deriving sexp]

    let rec equal_module_t a b =
      String.equal a.name b.name
      && String.equal a.dir b.dir
      && Option.equal equal_module_t a.parent b.parent
    ;;

    type t =
      { current_module : module_t
      ; seen_files : module_t String.Table.t
      ; opened_modules : module_t list
      ; locals : mono String.Map.t
      ; ty_vars : mono String.Map.t
      ; ty_var_counter : Counter.t
      ; var_counter : Counter.t
      ; seen_vars : String.Hash_set.t
      ; seen_types : String.Hash_set.t
      ; ty_var_map : mono String.Table.t option
      ; user_type_to_path : string list String.Table.t
      }
    [@@deriving sexp]
  end

  include T

  let default_types () = String.Table.of_alist_exn []

  let rec unique_name t =
    let name = internal_var t.var_counter in
    if Hash_set.mem t.seen_vars name
    then unique_name t
    else (
      Hash_set.add t.seen_vars name;
      name)
  ;;

  let full_path module_t =
    let rec go acc module_t =
      let acc = module_t.name :: acc in
      match module_t.parent with
      | None -> acc
      | Some p -> go acc p
    in
    go [] module_t
  ;;

  let module_prefix module_t =
    let buf = Buffer.create 16 in
    let rec go module_t =
      (match module_t.parent with
       | None -> ()
       | Some p -> go p);
      Buffer.add_string buf module_t.name;
      Buffer.add_char buf '_'
    in
    go module_t;
    Buffer.contents buf
  ;;

  let register_name ~state name =
    match Hash_set.mem state.seen_vars name with
    | false -> Hash_set.add state.seen_vars name
    | true -> failwith [%string "Name linked multiple times: `%{name}`"]
  ;;

  let make_unique_helper ~state name =
    let prefix = module_prefix state.current_module in
    let name = prefix ^ name in
    let rec loop i =
      let name = name ^ Int.to_string i in
      match Hash_set.mem state.seen_vars name with
      | false ->
        Hash_set.add state.seen_vars name;
        name
      | true -> loop (i + 1)
    in
    match Hash_set.mem state.seen_vars name with
    | false ->
      Hash_set.add state.seen_vars name;
      name
    | true -> loop 0
  ;;

  let make_unique ~state name =
    match name with
    | "main" when Hash_set.mem state.seen_vars "main" ->
      failwith "Duplicate main functions"
    | "main" ->
      Hash_set.add state.seen_vars name;
      name
    | _ -> make_unique_helper ~state name
  ;;

  let make_unique_type ~state name =
    let prefix = module_prefix state.current_module in
    let name = prefix ^ name in
    let rec loop i =
      let name = name ^ Int.to_string i in
      match Hash_set.mem state.seen_types name with
      | false ->
        Hash_set.add state.seen_types name;
        name
      | true -> loop (i + 1)
    in
    match Hash_set.mem state.seen_types name with
    | false ->
      Hash_set.add state.seen_types name;
      name
    | true -> loop 0
  ;;

  let module_create ~parent ~name ~dir =
    { name
    ; dir
    ; sub_modules = String.Table.create ()
    ; glob_vars = String.Table.create ()
    ; types = default_types ()
    ; variant_to_type = String.Table.create ()
    ; field_to_type = String.Table.create ()
    ; in_eval = false
    ; parent
    }
  ;;

  let create filename =
    let dir, name = unel2_file filename in
    let current_module = module_create ~parent:None ~name ~dir in
    { current_module
    ; opened_modules = []
    ; seen_files = String.Table.of_alist_exn [ filename, current_module ]
    ; locals = String.Map.empty
    ; ty_vars = String.Map.empty
    ; ty_var_counter = Counter.create ()
    ; var_counter = Counter.create ()
    ; seen_vars = String.Hash_set.create ()
    ; seen_types = String.Hash_set.create ()
    ; ty_var_map = None
    ; user_type_to_path = String.Table.create ()
    }
  ;;

  let lookup_module_in names ~in_:module_t =
    let rec loop m names' =
      match names' with
      | [] -> Ok m
      | name :: names' ->
        (match Hashtbl.find m.sub_modules name with
         | Some m -> loop m names'
         | None -> Error name)
    in
    loop module_t names
  ;;

  let lookup_module_in_exn names ~in_ =
    match lookup_module_in names ~in_ with
    | Ok a -> a
    | Error name ->
      failwith
        [%string
          "Unknown module `%{name}` in chain `%{String.concat ~sep:\" \" \
           names}`"]
  ;;

  let lookup_module_exn ~state ~if_missing names =
    match names with
    | [] -> state.current_module
    | fst :: _ ->
      (match Hashtbl.find state.current_module.sub_modules fst with
       | None -> if_missing fst
       | _ -> ());
      lookup_module_in_exn names ~in_:state.current_module
  ;;

  let rec try_on_all_modules state ~try_make_module ~module_path ~f =
    let rec loop opened_modules =
      match opened_modules with
      | [] ->
        Option.bind state.current_module.parent ~f:(fun parent ->
          let state =
            { state with current_module = parent; opened_modules = [] }
          in
          try_on_all_modules state ~try_make_module ~module_path ~f)
      | module_t :: opened_modules ->
        (match f module_path module_t with
         | Some _ as res -> res
         | None -> loop opened_modules)
    in
    match f module_path state.current_module with
    | Some _ as res -> res
    | None ->
      let on_newly_created =
        match module_path with
        | [] -> None
        | fst :: rest -> Option.bind (try_make_module ~state fst) ~f:(f rest)
      in
      (match on_newly_created with
       | Some _ as res -> res
       | None -> loop state.opened_modules)
  ;;
end

type expr = Type_state.module_t list Typed_ast.expr
type expr_inner = Type_state.module_t list Typed_ast.expr_inner
type gen_expr = Type_state.module_t list Typed_ast.gen_expr
type var = Type_state.module_t list Typed_ast.var
type top_var = Type_state.module_t list Typed_ast.top_var

let make_user_type ~repr_name ~name ~ty_vars =
  { repr_name; name; ty_vars; info = ref None }
;;

type ty_var_map = mono String.Map.t [@@deriving sexp]
type locals_map = mono String.Map.t

let empty_ty_vars : ty_var_map = String.Map.empty

let poly_inner (poly : poly) =
  let rec go = function
    | `Mono mono -> mono
    | `For_all (_, r) -> go r
  in
  go poly
;;

let rec pretty_print_module_t module_t =
  let open PPrint in
  let user_types =
    Hashtbl.to_alist module_t.Type_state.types
    |> List.map ~f:(fun (name, user_type) ->
      string [%string "type %{name} ="]
      ^^ space
      ^^ Pretty_print.user_type_p user_type)
    |> separate (break 1)
  in
  let glob_vars =
    Hashtbl.to_alist module_t.glob_vars
    |> List.map ~f:(fun (name, var) ->
      match var with
      | Typed_ast.El { poly; _ } ->
        string "let"
        ^^ space
        ^^ string name
        ^^ space
        ^^ colon
        ^^ space
        ^^ Pretty_print.mono (poly_inner poly)
      | Extern (name, _, mono) ->
        string [%string "extern %{name} : %{show_mono mono}"]
      | Implicit_extern (name, _, mono) ->
        string [%string "implicit_extern %{name} : %{show_mono mono}"])
    |> separate (break 1)
  in
  let modules =
    Hashtbl.to_alist module_t.sub_modules
    |> List.map ~f:(fun (name, module_t) ->
      string [%string "module %{name} ="]
      ^^ space
      ^^ pretty_print_module_t module_t)
    |> separate (break 1)
  in
  concat
    [ string [%string "Module %{module_t.Type_state.name}:"]
    ; nest 4 (hardline ^^ user_types)
    ; nest 4 (hardline ^^ modules)
    ; nest 4 (hardline ^^ glob_vars)
    ]
;;

let get_ty_var ~state name =
  Option.first_some
    (Map.find state.Type_state.ty_vars name)
    (Option.bind state.ty_var_map ~f:(fun ty_var_map ->
       Hashtbl.find ty_var_map name))
;;

let get_non_user_type ~make_ty_vars ~state name =
  let gen_ty_var () =
    Option.map state.Type_state.ty_var_map ~f:(fun ty_var_map ->
      let indir = make_indir () in
      Hashtbl.set ty_var_map ~key:name ~data:indir;
      indir)
    |> Option.value_or_thunk ~default:(fun () ->
      failwith [%string "Unknown type `%{name}`"])
  in
  match name with
  | "i64" -> `I64
  | "c_int" -> `C_int
  | "f64" -> `F64
  | "bool" -> `Bool
  | "char" -> `Char
  | "unit" -> `Unit
  | "_" when make_ty_vars -> make_indir ()
  | "_" -> failwith "Cannot make unknown ty_var `_` in this context"
  | _ ->
    (match get_ty_var ~state name with
     | None -> gen_ty_var ()
     | Some a -> a)
;;

let find_module_in_submodules ~state ~try_make_module ~f module_path =
  Type_state.try_on_all_modules
    ~f:(fun module_path module_t ->
      match Type_state.lookup_module_in ~in_:module_t module_path with
      | Error _ -> None
      | Ok module_t -> f module_t)
    ~try_make_module
    ~module_path
    state
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

let gen_expr ~counter ~vars ~indirs (expr : expr) : gen_expr =
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

let make_vars_weak_expr ~vars ~indirs (expr : expr) : gen_expr =
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

let rec try_make_module ~state name =
  let filename = el2_file state.Type_state.current_module.dir name in
  match Stdlib.Sys.file_exists filename with
  | false -> None
  | true -> Some (process_file ~state filename)

and get_user_type_variant_exn ~variant inst_user_type =
  let insted = inst_user_type_exn inst_user_type in
  match get_user_type_variant insted variant with
  | Some x -> x
  | None -> failwith [%string "Unknown variant %{variant}"]

and get_user_type_variant_with_data_exn ~variant inst_user_type =
  get_user_type_variant_exn inst_user_type ~variant
  |> Option.value_or_thunk ~default:(fun () ->
    failwith
      [%string
        {| Variant does not have any data: `%{variant}`
               in %{show_mono (`User inst_user_type)}|}])

and get_user_type_variant_without_data_exn ~variant inst_user_type =
  match get_user_type_variant_exn inst_user_type ~variant with
  | None -> ()
  | Some _ ->
    failwith
      [%string
        {| Variant has data: `%{variant}`
               in %{show_mono (`User inst_user_type)}|}]

and lookup_and_inst_user_type ~state (path : string path) =
  let user_type = lookup_user_type ~state path in
  inst_user_type_gen user_type

and get_user_type_from_field_exn ~state field =
  let user_type' = lookup_field ~state field in
  let inst_user_type = inst_user_type_gen user_type' in
  let res_type = get_user_type_field_exn inst_user_type ~field:field.inner in
  inst_user_type, res_type

and get_user_type_from_variant_exn ~state variant =
  let user_type' = lookup_variant ~state variant in
  let inst_user_type = inst_user_type_gen user_type' in
  let res_type =
    get_user_type_variant_with_data_exn inst_user_type ~variant:variant.inner
  in
  inst_user_type, res_type

and get_user_type_from_variant_no_data_exn ~state variant =
  let user_type' = lookup_variant ~state variant in
  let inst_user_type = inst_user_type_gen user_type' in
  get_user_type_variant_without_data_exn inst_user_type ~variant:variant.inner;
  inst_user_type

and get_struct_list_exn ~state s =
  let user_type = lookup_and_inst_user_type ~state s in
  ( user_type
  , (match get_insted_user_type user_type with
     | Some { info = { contents = Some (`Struct l) }; _ } -> l
     | _ -> failwith [%string "Not a struct: %{show_path Fn.id s}"])
    |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b) )

and get_user_type_field_exn ~field inst_user_type =
  let insted = inst_user_type_exn inst_user_type in
  match get_user_type_field insted field with
  | Some x -> x
  | None -> failwith [%string "Unknown field %{field}"]

and lookup_var_opt ~state { inner = name; module_path } =
  let f module_t = Hashtbl.find module_t.Type_state.glob_vars name in
  find_module_in_submodules ~try_make_module ~state ~f module_path

and lookup_var ~state p =
  match lookup_var_opt ~state p with
  | None -> failwith [%string "Unknown variable %{show_path Fn.id p}"]
  | Some x -> x

and lookup_user_type_opt ~state ({ module_path; inner = name } : string path) =
  let f module_t = Hashtbl.find module_t.Type_state.types name in
  find_module_in_submodules ~try_make_module ~state module_path ~f

and lookup_user_type ~state (p : string path) =
  match lookup_user_type_opt ~state p with
  | None -> failwith [%string "Unknown type %{show_path Fn.id p}"]
  | Some x -> x

and lookup_variant ~state { module_path; inner = name } =
  let f module_t = Hashtbl.find module_t.Type_state.variant_to_type name in
  match find_module_in_submodules ~try_make_module ~state module_path ~f with
  | None -> failwith [%string "Unknown variant %{name}"]
  | Some x -> x

and lookup_field ~state { module_path; inner = name } =
  let f module_t = Hashtbl.find module_t.Type_state.field_to_type name in
  match find_module_in_submodules ~try_make_module ~state module_path ~f with
  | None -> failwith [%string "Unknown field %{name}"]
  | Some x -> x

and lookup_mono ~make_ty_vars ~state name =
  match
    get_ty_var ~state name, lookup_user_type_opt ~state (empty_path name)
  with
  | Some x, _ -> x
  | _, None -> get_non_user_type ~make_ty_vars ~state name
  | _, Some r ->
    (match r.ty_vars with
     | [] -> `User (inst_user_type_gen r)
     | _ -> failwith [%string "Type %{name} requires type arguments"])

and mono_of_type_expr ?(make_ty_vars = true) ~state (type_expr : type_expr)
  : mono
  =
  let f = mono_of_type_expr ~make_ty_vars ~state in
  match type_expr with
  | `Unit -> `Unit
  | `Named { inner; module_path = [] } -> lookup_mono ~make_ty_vars ~state inner
  | `Named path ->
    let r = lookup_user_type ~state path in
    (match r.ty_vars with
     | [] -> `User (inst_user_type_gen r)
     | _ ->
       failwith [%string "Type %{show_path Fn.id path} requires type arguments"])
  | `Pointer m -> `Pointer (f m)
  | `Tuple l -> `Tuple (List.map l ~f)
  | `Named_args (s, l) ->
    let monos = List.map l ~f in
    let user_type = lookup_user_type ~state s in
    let inst = inst_user_type ~monos user_type in
    `User inst
  | `Function (a, b) -> `Function (f a, f b)

and all_user_of_enum ~state l =
  let variants = String.Hash_set.create () in
  ( `Enum
      (List.map l ~f:(fun (s, t) ->
         if Hash_set.mem variants s
         then failwith [%string "Duplicate variant %{s}"];
         let mono_opt =
           Option.map t ~f:(mono_of_type_expr ~make_ty_vars:false ~state)
         in
         Hash_set.add variants s;
         s, mono_opt))
  , variants )

and all_user_of_struct ~state l =
  let set = Hash_set.create (module String) in
  ( `Struct
      (List.map l ~f:(fun (s, t) ->
         if Hash_set.mem set s then failwith [%string "Duplicate field %{s}"];
         Hash_set.add set s;
         s, mono_of_type_expr ~make_ty_vars:false ~state t))
  , set )

and process_types ~(state : Type_state.t) types =
  Hashtbl.iteri state.current_module.types ~f:(fun ~key ~data:user_type ->
    let ty_vars, decl, opened_modules = Hashtbl.find_exn types key in
    let ty_vars =
      List.fold ty_vars ~init:empty_ty_vars ~f:(fun acc s ->
        let mono = make_var_mono s in
        Map.add_exn acc ~key:s ~data:mono)
    in
    let state = { state with ty_vars; opened_modules } in
    let variants_f s =
      match
        Hashtbl.add state.current_module.variant_to_type ~key:s ~data:user_type
      with
      | `Ok -> ()
      | `Duplicate -> failwith [%string "Duplicate variant %{s}"]
    in
    let fields_f s =
      match
        Hashtbl.add state.current_module.field_to_type ~key:s ~data:user_type
      with
      | `Ok -> ()
      | `Duplicate -> failwith [%string "Duplicate field %{s}"]
    in
    let all_user =
      try
        match decl with
        | `Alias type_expr ->
          let mono' = mono_of_type_expr ~make_ty_vars:false ~state type_expr in
          (match last_user_type_info_not_insted mono' with
           | Some (`Enum l) ->
             List.map ~f:fst l
             |> List.iter ~f:(fun s ->
               Hashtbl.set
                 state.current_module.variant_to_type
                 ~key:s
                 ~data:user_type)
           | Some (`Struct l) ->
             List.map ~f:fst l
             |> List.iter ~f:(fun s ->
               Hashtbl.set
                 state.current_module.field_to_type
                 ~key:s
                 ~data:user_type)
           | _ -> ());
          `Alias mono'
        | `Enum l ->
          let all_user, variants = all_user_of_enum ~state l in
          Hash_set.iter ~f:variants_f variants;
          all_user
        | `Struct l ->
          let all_user, fields = all_user_of_struct ~state l in
          Hash_set.iter ~f:fields_f fields;
          all_user
      with
      | e ->
        let sexp = [%sexp_of: type_decl] decl |> Sexp.to_string_hum in
        print_endline [%string "Failed to define type %{key}: %{sexp}"];
        raise e
    in
    user_type.info := Some all_user);
  let seen_types = String.Hash_set.create () in
  Hashtbl.iter state.current_module.types ~f:(fun u ->
    if Hash_set.mem seen_types u.repr_name
    then ()
    else (
      try
        Hash_set.add seen_types u.repr_name;
        inf_type_check
          ~seen_types:(String.Hash_set.create ())
          ~in_path:String.Set.empty
          u
      with
      | Infinite_type x ->
        failwith
          [%string
            "Infinite type: %{u.name} is reachable from itself through %{x} \
             (in module %{state.current_module.name})"]))

and inf_type_check ~seen_types ~in_path u =
  if Set.mem in_path u.repr_name then raise (Infinite_type u.name);
  match Hash_set.mem seen_types u.repr_name, !(u.info) with
  | true, _ -> ()
  | _, None -> ()
  | false, Some x ->
    Hash_set.add seen_types u.repr_name;
    let in_path = Set.add in_path u.repr_name in
    (match x with
     | `Alias mono -> inf_type_check_mono ~from:u ~seen_types ~in_path mono
     | `Struct l ->
       List.iter l ~f:(fun (_, mono) ->
         inf_type_check_mono ~from:u ~seen_types ~in_path mono)
     | `Enum l ->
       List.iter l ~f:(fun (_, o) ->
         Option.iter o ~f:(fun mono ->
           inf_type_check_mono ~from:u ~seen_types ~in_path mono)))

and inf_type_check_mono ~from ~seen_types ~in_path mono =
  let rep = inf_type_check_mono ~from ~seen_types ~in_path in
  match mono with
  | `Bool | `I64 | `F64 | `Unit | `Char | `C_int -> ()
  | `User u when Set.mem in_path u.orig_user_type.repr_name ->
    raise (Infinite_type from.name)
  | `User u -> inf_type_check ~seen_types ~in_path u.orig_user_type
  | `Pointer mono ->
    inf_type_check_mono ~from ~seen_types ~in_path:String.Set.empty mono
  | `Tuple l -> List.iter l ~f:rep
  | `Indir _ -> ()
  | `Var _ -> ()
  | `Function (a, b) ->
    rep a;
    rep b
  | `Opaque m -> rep m

and breakup_patterns ~state ~vars (pattern : pattern) (expr : Ast.expr) =
  let rep = breakup_patterns ~state ~vars in
  let enqueue_new expanded_expr =
    let var = Type_state.unique_name state in
    Stack.push vars (var, expanded_expr);
    empty_path var
  in
  match pattern with
  | `Bool _ | `Float _ | `Char _ | `String _ | `Int _ | `Null ->
    failwith
      [%string
        "Refutable pattern `%{Sexp.to_string_hum [%sexp (pattern : pattern)]}`"]
  | `Var name -> Stack.push vars (name, expand_expr ~state expr)
  | `Unit ->
    (ignore : string path -> unit)
      (enqueue_new (`Typed (expand_expr ~state expr, `Unit)))
  | `Tuple l ->
    let len = List.length l in
    let var = enqueue_new (expand_expr ~state expr) in
    List.iteri l ~f:(fun i p ->
      let expr = `Tuple_access (`Var var, i, Some len) in
      rep p expr)
  | `Ref p ->
    let var = enqueue_new (expand_expr ~state expr) in
    rep p (`Deref (`Var var))
  | `Struct (type_name, l) ->
    let var =
      enqueue_new (`Assert_struct (type_name, expand_expr ~state expr))
    in
    List.iter l ~f:(fun (field, opt_p) ->
      let expr = `Field_access (`Var var, { type_name with inner = field }) in
      let p = Option.value opt_p ~default:(`Var field) in
      rep p expr)
  | `Typed (p, type_expr) ->
    let var = enqueue_new (`Typed (expand_expr ~state expr, type_expr)) in
    rep p (`Var var)
  | `Enum (name, opt_p) ->
    (match opt_p with
     | Some p ->
       let var =
         enqueue_new (`Access_enum_field (name, expand_expr ~state expr))
       in
       rep p (`Var var)
     | None ->
       (ignore : string path -> unit)
         (enqueue_new
            (`Assert_empty_enum_field (name, expand_expr ~state expr))))

and expand_let ~state ~init (p, a) =
  let vars = Stack.create () in
  breakup_patterns ~state ~vars p a;
  Stack.fold vars ~init ~f:(fun acc (var, expr) -> `Let (var, expr, acc))

and expand_expr ~state (expr : Ast.expr) : expanded_expr =
  let f = expand_expr ~state in
  match (expr : Ast.expr) with
  | `Null -> `Null
  | `Unit -> `Unit
  | `Bool b -> `Bool b
  | `Var s -> `Var s
  | `Int i -> `Int i
  | `Float f -> `Float f
  | `Char c -> `Char c
  | `String s -> `String s
  | `Question_mark a -> `Question_mark (f a)
  | `Enum s -> `Enum s
  | `Assert a -> `Assert (f a)
  | `Array_lit l -> `Array_lit (List.map l ~f)
  | `Tuple l -> `Tuple (List.map l ~f)
  | `Loop a -> `Loop (f a)
  | `Break a -> `Break (f a)
  | `Compound l ->
    let expr =
      List.fold_right l ~init:None ~f:(fun x acc ->
        match x, acc with
        | `Expr e, None -> Some (f e)
        | `Expr e, Some r -> `Let ("_", f e, r) |> Option.some
        | `Let (a, b), None ->
          expand_let ~state ~init:`Unit (a, b) |> Option.some
        | `Let (a, b), Some r -> expand_let ~state ~init:r (a, b) |> Option.some)
      |> Option.value ~default:`Unit
    in
    `Compound expr
  | `Index (a, b) -> `Index (f a, f b)
  | `Inf_op (op, a, b) -> `Inf_op (op, f a, f b)
  | `Assign (a, b) -> `Assign (f a, f b)
  | `Apply (a, b) -> `Apply (f a, f b)
  | `Tuple_access (a, i, o) -> `Tuple_access (f a, i, o)
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
    let init = expand_expr ~state b in
    expand_let ~state ~init (p, a)

and function_arg_set ~init l =
  List.fold l ~init ~f:(fun acc ->
      function
      | `Untyped s -> Set.add acc s
      | `Typed (s, _) -> Set.add acc s)

and pattern_vars p ~locals =
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

and traverse_expr_var_part ~state ~not_found_vars ~edge ~locals var =
  match var with
  | { inner = name'; module_path = [] } when Set.mem locals name' -> `Local
  | { inner = name'; module_path } ->
    let f module_t =
      Hashtbl.find module_t.Type_state.glob_vars name'
      |> Option.map ~f:(fun var -> var, module_t)
    in
    (match find_module_in_submodules ~try_make_module ~state ~f module_path with
     | None ->
       Typed_ast.(edge.used_globals <- Set.add edge.used_globals name');
       Hashtbl.add_multi not_found_vars ~key:name' ~data:edge.comptime;
       `Global
     | Some (var, module_t)
       when Type_state.equal_module_t state.Type_state.current_module module_t
       ->
       Typed_ast.(edge.used_globals <- Set.add edge.used_globals name');
       Typed_ast.unify_var_comptimes ~user:(El edge) ~used:var;
       `Global
     | Some (var, _) ->
       Typed_ast.unify_var_comptimes ~user:(El edge) ~used:var;
       `Global)

and traverse_expr ~state ~not_found_vars ~edge ~locals (expr : expanded_expr) =
  let rep = traverse_expr ~state ~not_found_vars ~edge in
  match expr with
  | `Bool _ | `Int _ | `Float _ | `Char _ | `String _ | `Enum _ | `Unit | `Null
  | `Size_of (`Type _) -> ()
  | `Var v ->
    ignore (traverse_expr_var_part ~state ~not_found_vars ~edge ~locals v)
  | `Match (a, l) ->
    rep ~locals a;
    List.iter l ~f:(fun (p, e) -> rep ~locals:(pattern_vars p ~locals) e)
  | `Tuple l | `Array_lit l -> List.iter l ~f:(rep ~locals)
  | `Assign (`Var v, b) ->
    (* can only assign to locals *)
    (match traverse_expr_var_part ~state ~not_found_vars ~edge ~locals v with
     | `Local -> ()
     | `Global -> Typed_ast.unify_comptime_var ~user:edge.comptime ~used:`False);
    rep ~locals b
  | `Index (a, b) | `Inf_op (_, a, b) | `Apply (a, b) | `Assign (a, b) ->
    rep ~locals a;
    rep ~locals b
  | `Let (s, a, b) ->
    let locals = Set.add locals s in
    let rep = rep ~locals in
    rep a;
    rep b
  | `Ref a | `Deref a ->
    Typed_ast.unify_comptime_var ~user:edge.comptime ~used:`False;
    rep ~locals a
  | `Break a
  | `Loop a
  | `Assert a
  | `Compound a
  | `Question_mark a
  | `Return a
  | `Size_of (`Expr a)
  | `Unsafe_cast a
  | `Assert_struct (_, a)
  | `Access_enum_field (_, a)
  | `Assert_empty_enum_field (_, a)
  | `Tuple_access (a, _, _)
  | `Field_access (a, _)
  | `Pref_op (_, a)
  | `Typed (a, _) -> rep ~locals a
  | `Struct (_, l) ->
    List.iter l ~f:(fun (field_name, o) ->
      match o with
      | Some p -> rep ~locals p
      | None -> rep ~locals (`Var { inner = field_name; module_path = [] }))
  | `If (a, b, c) ->
    rep ~locals a;
    rep ~locals b;
    rep ~locals c

and process_module ~opened_modules ~state ~module_t toplevels =
  module_t.Type_state.in_eval <- true;
  type_check
    ~state:
      { state with
        Type_state.current_module = module_t
      ; opened_modules
      ; locals = String.Map.empty
      }
    toplevels;
  module_t.in_eval <- false;
  module_t

and process_file ?parent ~state filename =
  match Hashtbl.find state.Type_state.seen_files filename with
  | Some m when phys_equal m state.Type_state.current_module -> m
  | Some (Type_state.{ in_eval = false; _ } as m) -> m
  | Some { in_eval = true; _ } ->
    raise
      (Module_cycle
         { offending_module = filename
         ; from_module = state.current_module.name
         })
  | None ->
    In_channel.with_file filename ~f:(fun chan ->
      let lexbuf = Lexing.from_channel chan in
      Frontend.parse_and_do ~filename lexbuf ~f:(fun toplevels ->
        let dir, name = unel2_file filename in
        let module_t = Type_state.module_create ~parent ~name ~dir in
        Hashtbl.set state.seen_files ~key:filename ~data:module_t;
        process_module ~opened_modules:[] ~state ~module_t toplevels))

and process_module_path ?parent ~state path =
  match path with
  | fst :: rest ->
    let filename = el2_file state.Type_state.current_module.dir fst in
    let in_ = process_file ?parent ~state filename in
    Type_state.lookup_module_in_exn ~in_ rest
  | _ -> failwith "impossible"

and type_check ~state toplevels =
  try
    let state = process_toplevel_graph ~state toplevels in
    let _ = get_sccs state.Type_state.current_module.glob_vars in
    Hashtbl.iter state.current_module.glob_vars ~f:(fun var ->
      let state =
        match var with
        | Typed_ast.El { data = opened_modules; _ } ->
          { state with opened_modules }
        | _ -> state
      in
      ignore (infer_var ~state var))
  with
  | Failure s as exn ->
    print_endline
      [%string
        "Fatal error while evaluating %{state.current_module.name}:\n%{s}"];
    Backtrace.Exn.most_recent_for_exn exn
    |> Option.value_exn
    |> Backtrace.to_string
    |> print_endline;
    exit 1

and process_toplevel_graph ~state (toplevels : toplevel list) =
  let type_defs = String.Table.create () in
  let let_toplevels = Queue.create () in
  let _ =
    (* TODO: make type processing happen as we go, since this is now needed with
       sub modules *)
    List.fold toplevels ~init:state.opened_modules ~f:(fun acc ->
        function
        | `Open_file filename ->
          let nek =
            process_file
              ~state
              (Filename.concat state.current_module.dir filename)
          in
          Queue.enqueue let_toplevels (`Open nek);
          nek :: acc
        | `Open path ->
          let nek = process_module_path ~state path in
          Queue.enqueue let_toplevels (`Open nek);
          nek :: acc
        | `Let_type ((name, ty_vars), type_decl) ->
          let repr_name = Type_state.make_unique_type ~state name in
          Hashtbl.set
            state.Type_state.user_type_to_path
            ~key:repr_name
            ~data:(Type_state.full_path state.current_module);
          (match
             Hashtbl.add
               state.Type_state.current_module.types
               ~key:name
               ~data:(make_user_type ~repr_name ~ty_vars ~name)
           with
           | `Ok ->
             Hashtbl.add_exn type_defs ~key:name ~data:(ty_vars, type_decl, acc)
           | `Duplicate -> failwith [%string "Duplicate type %{name}"]);
          acc
        | `Let_fn x ->
          Queue.enqueue let_toplevels (`Let_fn x);
          acc
        | `Let x ->
          Queue.enqueue let_toplevels (`Let x);
          acc
        | `Extern x ->
          Queue.enqueue let_toplevels (`Extern x);
          acc
        | `Implicit_extern x ->
          Queue.enqueue let_toplevels (`Implicit_extern x);
          acc
        | `Module_decl (name, toplevels) ->
          (* define the submodule. it can use anything we've defined so far,
             but not polymorphically (a bit weird but eh) *)
          let module_t =
            Type_state.module_create
              ~parent:(Some state.current_module)
              ~name
              ~dir:state.current_module.dir
          in
          let module_t =
            process_module ~opened_modules:acc ~state ~module_t toplevels
          in
          (match
             Hashtbl.add
               state.current_module.sub_modules
               ~key:name
               ~data:module_t
           with
           | `Ok -> acc
           | _ -> failwith [%string "Duplicate submodule %{name}"]))
  in
  let not_found_vars = String.Table.create () in
  process_types ~state type_defs;
  let find_references ~edge ~state ~locals expr =
    let open Typed_ast in
    match Hashtbl.find state.Type_state.current_module.glob_vars edge.name with
    | Some _ -> failwith [%string "Duplicate variable %{edge.name}"]
    | None ->
      Hashtbl.add_exn
        state.current_module.glob_vars
        ~key:edge.name
        ~data:(El edge);
      (match Hashtbl.find_and_remove not_found_vars edge.name with
       | None -> ()
       | Some l ->
         List.iter l ~f:(fun x ->
           Typed_ast.unify_comptime_var ~used:edge.comptime ~user:x));
      (try traverse_expr ~state ~not_found_vars ~edge ~locals expr with
       | exn ->
         print_endline [%string "Error while processing %{edge.name}:"];
         raise exn)
  in
  let _ =
    Queue.fold let_toplevels ~init:[] ~f:(fun opened_modules ->
        function
        | `Open m -> m :: opened_modules
        | `Let_fn (name, vars, expr) ->
          let ty_var_map = String.Table.create () |> Option.some in
          let state = { state with ty_var_map; opened_modules } in
          let expr = expand_expr ~state expr in
          let var_decls =
            List.map vars ~f:(function
              | `Typed (s, e) -> s, mono_of_type_expr ~state e
              | `Untyped s -> s, make_indir ())
          in
          let edge =
            Typed_ast.create_func
              ~name
              ~expr
              ~var_decls
              ~ty_var_map
              ~data:opened_modules
              ~unique_name:(Type_state.make_unique ~state name)
          in
          find_references
            ~state
            ~edge
            ~locals:(function_arg_set ~init:String.Set.empty vars)
            expr;
          opened_modules
        | `Let (pattern, expr) ->
          let vars = Stack.create () in
          let ty_var_map = String.Table.create () |> Option.some in
          let state = { state with ty_var_map; opened_modules } in
          breakup_patterns ~state ~vars pattern expr;
          Stack.iter vars ~f:(fun (name, expr) ->
            let edge =
              Typed_ast.create_non_func
                ~name
                ~expr
                ~ty_var_map
                ~data:opened_modules
                ~unique_name:(Type_state.make_unique ~state name)
            in
            find_references ~state ~edge ~locals:String.Set.empty expr);
          opened_modules
        | `Extern (name, t, extern_name) ->
          let ty_var_map = String.Table.create () |> Option.some in
          let state = { state with ty_var_map; opened_modules } in
          let mono = mono_of_type_expr ~state t in
          Type_state.register_name ~state extern_name;
          let edge = Typed_ast.Extern (name, extern_name, mono) in
          (match
             Hashtbl.add state.current_module.glob_vars ~key:name ~data:edge
           with
           | `Ok -> opened_modules
           | _ -> failwith [%string "Duplicate variable %{name}"])
        | `Implicit_extern (name, t, extern_name) ->
          let ty_var_map = String.Table.create () |> Option.some in
          let state = { state with ty_var_map; opened_modules } in
          let mono = mono_of_type_expr ~state t in
          Type_state.register_name ~state extern_name;
          let edge = Typed_ast.Implicit_extern (name, extern_name, mono) in
          (match
             Hashtbl.add state.current_module.glob_vars ~key:name ~data:edge
           with
           | `Ok -> opened_modules
           | _ -> failwith [%string "Duplicate variable %{name}"]))
  in
  match Hashtbl.is_empty not_found_vars with
  | false ->
    failwith
      [%string
        "Unknown variables: `%{Hashtbl.keys not_found_vars |> String.concat \
         ~sep:\", \"}`"]
  | true -> state

and get_sccs glob_vars =
  let open Typed_ast in
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
  let num = ref 0 in
  Stack.iter res ~f:(fun vars ->
    if print_sccs then print_endline [%string "SCC %{!num#Int}:"];
    incr num;
    let scc = { vars; type_check_state = `Untouched } in
    Stack.iter vars ~f:(fun v ->
      if print_sccs then print_endline [%string "  %{v.name}"];
      v.scc <- scc));
  res

and mono_of_var ~state name =
  match Map.find state.Type_state.locals name with
  | Some x -> `Local x
  | None ->
    let var = lookup_var ~state (empty_path name) in
    `Global (var, infer_var ~state var)

and infer_var ~state (var : Type_state.module_t list Typed_ast.top_var) =
  match var with
  | El v ->
    infer_scc ~state v.scc;
    let mono, inst_map = inst v.poly in
    (match v.scc.type_check_state with
     | `Untouched | `In_checking -> mono, None
     | `Done -> mono, Some inst_map)
  | Extern (_, _, mono) | Implicit_extern (_, _, mono) ->
    mono, Some String.Map.empty

and infer_scc ~state scc =
  match scc.type_check_state with
  | `Done | `In_checking -> ()
  | `Untouched -> infer_scc_ ~state scc

and infer_scc_ ~state scc =
  let open Typed_ast in
  scc.type_check_state <- `In_checking;
  let monos =
    Stack.to_list scc.vars
    |> List.map ~f:(fun v ->
      try
        let state = { state with ty_var_map = v.ty_var_map } in
        let mono, _ = inst v.poly in
        let state, to_unify, mono =
          match v.args, mono with
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
        let expr_inner, mono' =
          type_expr ~res_type:to_unify ~break_type:None ~state v.expr
        in
        v, (expr_inner, unify to_unify mono'), mono
      with
      | Unification_error e ->
        show_unification_error e |> print_endline;
        print_s [%message "While evaluating" v.name (v.expr : expanded_expr)];
        exit 1)
  in
  let counter = Counter.create () in
  let vars = String.Table.create () in
  let indirs = Int.Table.create () in
  List.iter monos ~f:(fun (v, expr, mono) ->
    let mono = mono_map_rec_keep_refs mono ~f:inner_mono in
    let expr, poly =
      match v.args with
      | `Func l ->
        let expr = gen_expr ~counter ~vars ~indirs expr in
        let poly = gen ~counter ~vars ~indirs mono in
        let l =
          List.map l ~f:(fun (s, m) -> s, gen_mono ~counter ~vars ~indirs m)
        in
        v.args <- `Func l;
        expr, poly
      | `Non_func ->
        let vars = String.Table.create () in
        let indirs = Int.Table.create () in
        ( make_vars_weak_expr ~vars ~indirs expr
        , make_vars_weak ~vars ~indirs mono )
    in
    v.poly <- poly;
    v.typed_expr <- Some expr);
  scc.type_check_state <- `Done

and make_pointer ~state:_ =
  let ty_var = make_indir () in
  `Pointer ty_var, ty_var

and type_expr ~res_type ~break_type ~state expr =
  try type_expr_ ~res_type ~break_type ~state expr with
  | Unification_error _ as exn ->
    print_endline "While evaluating:";
    print_s [%message (expr : expanded_expr)];
    raise exn

and workout_enum_type_for_question_mark ~state ~res_type am =
  match inner_mono am with
  | `User u ->
    let module_path =
      Hashtbl.find_exn
        state.Type_state.user_type_to_path
        u.orig_user_type.repr_name
    in
    let insted = inst_user_type_exn u in
    let info = inner_info !(insted.info) in
    (match info with
     | Some (`Enum l) -> l, module_path
     | _ -> failwith [%string "question mark on non-enum (%{show_mono am})"])
  | `Indir _ ->
    let res_user_type =
      match inner_mono res_type with
      | `User u -> inst_user_type_gen u.orig_user_type
      | _ ->
        failwith "question mark on weak type - perhaps specify more type info"
    in
    let am = unify am (`User res_user_type) in
    workout_enum_type_for_question_mark ~state ~res_type am
  | _ -> failwith [%string "question mark on non-enum (%{show_mono am})"]

and type_expr_ ~res_type ~break_type ~state expr : expr =
  let rep ~state = type_expr ~res_type ~break_type ~state in
  match expr with
  | `Bool b -> `Bool b, `Bool
  | `Int i -> `Int i, `I64
  | `Null ->
    let pointer_type, _ = make_pointer ~state in
    `Null, pointer_type
  | `Return a ->
    let a, am = rep ~state a in
    let am = unify res_type am in
    `Return (a, am), make_indir ()
  | `Break a ->
    (match break_type with
     | Some break_type ->
       let a, am = rep ~state a in
       let am = unify break_type am in
       `Break (a, am), `Unit
     | None -> failwith "break outside of loop")
  | `Loop a ->
    let indir = make_indir () in
    let break_type = Some indir in
    let a, am = type_expr ~state ~res_type ~break_type a in
    `Loop (a, am), indir
  | `Float f -> `Float f, `F64
  | `Char c -> `Char c, `Char
  | `String s -> `String s, `Pointer `Char
  | `Unit -> `Unit, `Unit
  | `Var { inner = name; module_path = [] } ->
    (match mono_of_var ~state name with
     | `Global (var, (mono, inst_map)) -> `Glob_var (var, inst_map), mono
     | `Local mono -> `Local_var name, mono)
  | `Var p ->
    let var = lookup_var ~state p in
    let mono, inst_map = infer_var ~state var in
    `Glob_var (var, inst_map), mono
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
  | `Assert a ->
    let a, am = rep ~state a in
    let am = unify am `Bool in
    `Assert (a, am), `Unit
  | `Tuple_access (a, i, o) ->
    let a, am = rep ~state a in
    let am =
      match o with
      | None -> am
      | Some i ->
        let l = List.init i ~f:(fun _ -> make_indir ()) in
        unify am (`Tuple l)
    in
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
    let user_type = lookup_and_inst_user_type ~state str in
    let am = unify am (`User user_type) in
    a, am
  | `Question_mark a ->
    let _, am = rep ~state a in
    let variants, module_path =
      workout_enum_type_for_question_mark ~state ~res_type am
    in
    let fst, rest =
      match variants with
      | fst :: rest -> fst, rest
      | _ -> failwith "empty enum"
    in
    let make_enum_pattern field inner =
      match field with
      | false -> `Enum ({ module_path; inner }, None)
      | true -> `Enum ({ module_path; inner }, Some (`Var "x"))
    in
    let make_enum_ret_expr field inner =
      match field with
      | false -> `Return (`Enum { module_path; inner })
      | true ->
        `Return
          (`Apply
            ( `Enum { module_path; inner }
            , `Var { module_path = []; inner = "x" } ))
    in
    let fst_arm =
      match fst with
      | variant, None -> make_enum_pattern false variant, `Unit
      | variant, Some _ ->
        make_enum_pattern true variant, `Var { module_path = []; inner = "x" }
    in
    let rest_arms =
      List.map rest ~f:(fun (variant, field) ->
        let field = Option.is_some field in
        make_enum_pattern field variant, make_enum_ret_expr field variant)
    in
    let expr : expanded_expr = `Match (a, fst_arm :: rest_arms) in
    rep ~state expr
  | `Access_enum_field (field, a) ->
    let a, am = rep ~state a in
    let inst_user_type, res_type =
      get_user_type_from_variant_exn ~state field
    in
    let am = unify am (`User inst_user_type) in
    `Access_enum_field (field.inner, (a, am)), res_type
  | `Assert_empty_enum_field (field, a) ->
    let a, am = rep ~state a in
    let inst_user_type = get_user_type_from_variant_no_data_exn ~state field in
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
    let user_type, res_type = get_user_type_from_field_exn ~state field in
    let am = unify am (`User user_type) in
    `Field_access ((a, am), field.inner), res_type
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
    let l = List.sort l ~compare:(fun (a, _) (b, _) -> String.compare a b) in
    let user_type, struct_l = get_struct_list_exn ~state s in
    let l' =
      match List.zip struct_l l with
      | Ok l -> l
      | _ ->
        failwith [%string {| Wrong number of fields in struct `%{s.inner}`|}]
    in
    let l' =
      List.map l' ~f:(fun ((orig_field, orig_mono), (field, opt_expr)) ->
        if not (String.equal orig_field field)
        then raise (Unification_error End);
        let expr =
          match opt_expr with
          | Some expr -> expr
          | None -> `Var (empty_path field)
        in
        let a, am = rep ~state expr in
        let am = unify am orig_mono in
        field, (a, am))
    in
    `Struct l', `User user_type
  | `Apply (`Enum s, e) ->
    let inst_user_type, arg_type = get_user_type_from_variant_exn ~state s in
    let e, em = rep ~state e in
    let em = unify em arg_type in
    `Enum (s.inner, Some (e, em)), `User inst_user_type
  | `Enum s ->
    let inst_user_type = get_user_type_from_variant_no_data_exn ~state s in
    `Enum (s.inner, None), `User inst_user_type
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
    let var = Type_state.unique_name state in
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
        let conds = Typed_ast.And.(conds && conds') in
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
  | `Unit ->
    let _ = unify em `Unit in
    true_cond, (fun expr -> expr), state
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
    let l = List.sort l ~compare:(fun (a, _) (b, _) -> String.compare a b) in
    let user_type, struct_l = get_struct_list_exn ~state name in
    let l' =
      match List.zip struct_l l with
      | Ok l -> l
      | _ ->
        failwith [%string {| Wrong number of fields in struct `%{name.inner}`|}]
    in
    let em = unify em (`User user_type) in
    let expr = e, em in
    let conds = true_cond in
    let bindings_f expr = expr in
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
              {| Wrong field name in struct `%{name.inner}` (%{field} vs %{orig_field})|}];
        let pattern =
          match opt_pattern with
          | Some p -> p
          | None -> `Var field
        in
        let expr = `Field_access (expr, field), orig_mono in
        let conds', bindings_f', state =
          breakup_and_type_pattern ~state ~expr pattern
        in
        let conds = Typed_ast.And.(conds && conds') in
        let bindings_f expr = bindings_f (bindings_f' expr) in
        conds, bindings_f, state)
  | `Enum (name, opt_p) ->
    let user_type = lookup_variant ~state name in
    let user_type = inst_user_type_gen user_type in
    let arg_type = get_user_type_variant_exn user_type ~variant:name.inner in
    let em = unify em (`User user_type) in
    let conds = `Check_variant (name.inner, (e, em)), `Bool in
    (match opt_p with
     | Some p ->
       let arg_type =
         Option.value_or_thunk arg_type ~default:(fun () ->
           failwith [%string "variant does not have data `%{name.inner}`"])
       in
       let expr = `Access_enum_field (name.inner, (e, em)), arg_type in
       let conds', binding_f, state = breakup_and_type_pattern ~state ~expr p in
       let conds = Typed_ast.And.(conds && conds') in
       conds, binding_f, state
     | None ->
       if Option.is_some arg_type
       then failwith [%string "variant has data `%{name.inner}`"];
       conds, (fun expr -> expr), state)
;;

let type_check_starting_with ~filename =
  let state = Type_state.create filename in
  let res =
    In_channel.with_file filename ~f:(fun chan ->
      let lexbuf = Lexing.from_channel chan in
      Frontend.parse_and_do ~filename lexbuf ~f:(fun toplevels ->
        state.current_module.in_eval <- true;
        type_check ~state toplevels;
        state.current_module.in_eval <- false;
        state))
  in
  let has_main = lookup_var_opt ~state (empty_path "main") |> Option.is_some in
  res, has_main
;;

let type_check_and_output filename =
  try type_check_starting_with ~filename with
  | Unification_error e ->
    show_unification_error e |> print_endline;
    exit 1
  | Failure s ->
    print_endline "Fatal error:";
    print_endline s;
    exit 1
;;

let process_and_dump filename =
  let state, _ = type_check_and_output filename in
  Hashtbl.iter state.Type_state.seen_files ~f:(fun module_t ->
    pretty_print_module_t module_t |> Pretty_print.output_endline)
;;
