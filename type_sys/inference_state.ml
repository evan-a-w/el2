open! Core
open! Shared
open! Frontend
open! Ty

module Mono_ufds = Ufds.Make (struct
    type t = mono [@@deriving sexp, equal, compare]
  end)

type module_history =
  { current_name : Uppercase.t
  ; previous_modules : (Uppercase.t * Typed_ast.module_) list
  }
[@@deriving sexp, equal, compare, fields]

type binding_state =
  { name : Lowercase.t
  ; poly : poly
  }
[@@deriving sexp, equal, compare, fields]

type state =
  { mutable current_module_binding : Typed_ast.module_
  ; mutable current_path : Module_path.t
  ; mutable local_vars :
      (poly * binding_state ref * [ `Rec_or_global | `Not ] * [ `Arg | `Not ])
      list
      Lowercase.Map.t
  ; mutable module_history : module_history
  ; mutable symbol_n : int
  }
[@@deriving sexp, equal, compare, fields]

let add_module ~name ~module_bindings =
  let%bind state = State.Result.get in
  let current_module_binding = state.current_module_binding in
  let current_module_binding =
    { current_module_binding with
      toplevel_modules =
        Map.set
          current_module_binding.toplevel_modules
          ~key:name
          ~data:module_bindings
    }
  in
  state.current_module_binding <- current_module_binding
;;

let get_binding_id =
  let%bind state = State.Result.get in
  let res = state.binding_id_n in
  let%map () = State.Result.put { state with binding_id_n = res + 1 } in
  res
;;

let add_type_constructor arg name user_type type_proof =
  let%bind state = State.Result.get in
  let data = arg, user_type, type_proof in
  let type_id = type_proof.type_id in
  let%bind type_map =
    match Map.add state.type_map ~key:type_id ~data with
    | `Ok m -> return m
    | `Duplicate ->
      State.Result.error
        [%message
          "Duplicate type constructor" (name : Lowercase.t) (type_id : int)]
  in
  match
    Map.add
      state.current_module_binding.toplevel_type_constructors
      ~key:name
      ~data:type_id
  with
  | `Ok m ->
    State.Result.put
      { state with
        type_map
      ; current_module_binding =
          { state.current_module_binding with toplevel_type_constructors = m }
      }
  | `Duplicate ->
    State.Result.error
      [%message "Duplicate type constructor" (name : Lowercase.t)]
;;

let set_type_constructor arg name user_type type_proof =
  let%bind state = State.Result.get in
  let data = arg, user_type, type_proof in
  let type_id = type_proof.type_id in
  let type_map = Map.set state.type_map ~key:type_id ~data in
  let toplevel_type_constructors =
    Map.set
      state.current_module_binding.toplevel_type_constructors
      ~key:name
      ~data:type_id
  in
  State.Result.put
    { state with
      type_map
    ; current_module_binding =
        { state.current_module_binding with toplevel_type_constructors }
    }
;;

let set_current_module_binding current_module_binding =
  State.Result.modify (fun state -> { state with current_module_binding })
;;

let get_current_module_binding =
  let%map.State.Result state = State.Result.get in
  state.current_module_binding
;;

let empty_module_bindings path = empty_module_bindings path Typed_ast.empty_data

let empty_state path =
  { mono_ufds = Mono_ufds.empty
  ; mem_rep_ufds = Mem_rep.Abstract_ufds.empty
  ; current_path = path
  ; current_module_binding = empty_module_bindings path
  ; module_history = { current_name = ""; previous_modules = [] }
  ; symbol_n = 0
  ; binding_id_n = 0
  ; local_vars = Lowercase.Map.empty
  ; type_map = base_type_map
  ; binding_map = Binding_id.Map.empty
  }
;;

let gensym : string state_m =
  let open State.Let_syntax in
  let%bind state = State.get in
  let s = state.symbol_n in
  let%bind () = State.put { state with symbol_n = s + 1 } in
  let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
  let s = String.make 1 letter ^ Int.to_string (s / 26) in
  return s
;;

let print_ufds_map : unit state_result_m =
  let%map state = State.Result.get in
  print_s [%message (state.mono_ufds : Mono_ufds.t)]
;;

let add_type = add_type_constructor None

let add_module_var ?binding_id name poly =
  let%bind binding_id =
    match binding_id with
    | None -> get_binding_id
    | Some x -> return x
  in
  let%bind state = State.Result.get in
  let toplevel_vars =
    Map.add_multi
      state.current_module_binding.toplevel_vars
      ~key:name
      ~data:(poly, binding_id)
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  let binding_map =
    Map.set state.binding_map ~key:binding_id ~data:{ poly; name }
  in
  let%map () =
    State.Result.put { state with current_module_binding; binding_map }
  in
  binding_id
;;

let add_local_var ~is_rec ~is_arg ?binding_id name poly =
  let%bind binding_id =
    match binding_id with
    | None -> get_binding_id
    | Some x -> return x
  in
  let%bind state = State.Result.get in
  let is_rec =
    match is_rec with
    | true -> `Rec_or_global
    | false -> `Not
  in
  let is_arg =
    match is_arg with
    | true -> `Arg
    | false -> `Not
  in
  let local_vars =
    Map.add_multi
      state.local_vars
      ~key:name
      ~data:(poly, binding_id, is_rec, is_arg)
  in
  let binding_map =
    Map.set state.binding_map ~key:binding_id ~data:{ poly; name }
  in
  let%map () = State.Result.put { state with local_vars; binding_map } in
  binding_id
;;

let pop_local_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let local_vars = Map.remove_multi state.local_vars name in
  State.Result.put { state with local_vars }
;;

let pop_module_var name =
  let open State.Let_syntax in
  let%bind state = State.get in
  let toplevel_vars =
    Map.remove_multi state.current_module_binding.toplevel_vars name
  in
  let current_module_binding =
    { state.current_module_binding with toplevel_vars }
  in
  State.Result.put { state with current_module_binding }
;;

let find mono : mono state_m =
  let%bind.State state = State.get in
  let mono, mono_ufds = Mono_ufds.find state.mono_ufds mono in
  let%map.State () = State.put { state with mono_ufds } in
  mono
;;

let union mono1 mono2 : unit state_m =
  let%bind.State state = State.get in
  let mono_ufds = Mono_ufds.union state.mono_ufds mono1 mono2 in
  State.put { state with mono_ufds }
;;

let ufds_find mono =
  let%map.State state = State.get in
  Mono_ufds.find state.mono_ufds mono
;;

let rec search_modules
  : type a.
    Typed_ast.module_
    -> qualifications:Qualified.qualifications
    -> search_for:(Typed_ast.module_ -> a option)
    -> a option
  =
  let find_in_opened_modules module_bindings ~qualifications ~search_for =
    List.find_map
      module_bindings.opened_modules
      ~f:(search_modules ~qualifications ~search_for)
  in
  fun module_bindings
      ~qualifications
      ~(search_for : Typed_ast.module_ -> a option) ->
    match qualifications with
    | [] ->
      (match search_for module_bindings with
       | Some x -> Some x
       | None ->
         find_in_opened_modules module_bindings ~qualifications ~search_for)
    | name :: qualifications ->
      let open Option.Let_syntax in
      let first =
        Map.find module_bindings.toplevel_modules name
        >>= search_modules ~qualifications ~search_for
      in
      (match first with
       | Some _ -> first
       | None ->
         find_in_opened_modules module_bindings ~qualifications ~search_for)
;;

let find_module_binding qualifications =
  let%bind.State state = State.get in
  match
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:Option.some
  with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "module not found" (qualifications : Qualified.qualifications)]
;;

let lookup_type_map type_id =
  let%bind state = State.Result.get in
  match Map.find state.type_map type_id with
  | Some x -> State.Result.return x
  | None -> State.Result.error [%message "type not found" (type_id : int)]
;;

let lookup_type_constructor qualified_name =
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_type_constructors type_name)
  in
  match res with
  | Some type_id -> lookup_type_map type_id
  | None ->
    State.Result.error
      [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]
;;

let add_to_type_map ~type_id type_constructor =
  let%bind state = State.Result.get in
  match Map.add state.type_map ~key:type_id ~data:type_constructor with
  | `Ok type_map -> State.Result.put { state with type_map }
  | `Duplicate ->
    State.Result.error [%message "duplicate type id" (type_id : int)]
;;

let set_type_map ~type_id type_constructor =
  State.Result.modify (fun state ->
    let type_map = Map.set state.type_map ~key:type_id ~data:type_constructor in
    { state with type_map })
;;

let lookup_type ?(type_var = true) qualified_name =
  let qualifications, type_name = Qualified.split qualified_name in
  let type_var_fn = if type_var then Option.some else Fn.const None in
  let type_var_type =
    match qualifications with
    | [] -> type_var_fn (TyVar type_name)
    | _ -> None
  in
  let%bind res =
    match%map.State lookup_type_constructor qualified_name with
    | Ok (None, _, type_proof) -> Ok (Some (Named type_proof))
    | _ -> Ok None
  in
  match Option.first_some res type_var_type with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "type not found" (qualified_name : Lowercase.t Qualified.t)]
;;

let lookup_local_var name =
  let%map state = State.Result.get in
  match Map.find state.local_vars name with
  | Some (x :: _) -> Some x
  | _ -> None
;;

let lookup_var qualified_name : _ state_result_m =
  let%bind state = State.Result.get in
  let qualifications, type_name = Qualified.split qualified_name in
  match qualifications, Map.find state.local_vars type_name with
  | [], Some (x :: _) -> State.Result.return x
  | _ ->
    let res =
      search_modules
        state.current_module_binding
        ~qualifications
        ~search_for:(fun module_bindings ->
          Map.find module_bindings.toplevel_vars type_name)
    in
    (match res with
     | Some ((a, b) :: _) -> State.Result.return (a, b, `Rec_or_global, `Not)
     | None | Some [] ->
       State.Result.error
         [%message
           "var not in scope" (qualified_name : Lowercase.t Qualified.t)])
;;

let add_constructor name arg result =
  let%bind state = State.Result.get in
  match
    Map.add
      state.current_module_binding.toplevel_constructors
      ~key:name
      ~data:(arg, result)
  with
  | `Ok toplevel_constructors ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_constructors }
      }
  | `Duplicate ->
    State.Result.error
      [%message "duplicate constructor" ~constructor:(name : Uppercase.t)]
;;

let add_field field poly =
  let%bind state = State.Result.get in
  match
    Map.add state.current_module_binding.toplevel_fields ~key:field ~data:poly
  with
  | `Ok toplevel_fields ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_fields }
      }
  | `Duplicate ->
    State.Result.error [%message "duplicate field" ~field:(field : Lowercase.t)]
;;

let add_record field_map type_proof : _ state_result_m =
  let%bind field_set =
    Map.fold
      field_map
      ~init:(return Lowercase.Set.empty)
      ~f:(fun ~key ~data:(poly, mut) acc ->
        let%bind acc = acc in
        let%map () = add_field key (type_proof, mut, poly) in
        Set.add acc key)
  in
  let field_map = Lowercase.Map.map field_map ~f:fst in
  let%bind state = State.Result.get in
  match
    Map.add
      state.current_module_binding.toplevel_records
      ~key:field_set
      ~data:(field_map, type_proof)
  with
  | `Ok toplevel_records ->
    State.Result.put
      { state with
        current_module_binding =
          { state.current_module_binding with toplevel_records }
      }
  | `Duplicate ->
    State.Result.error
      [%message "duplicate record" (field_set : Lowercase.Set.t)]
;;

let lookup_record qualified_map =
  let%bind state = State.Result.get in
  let qualifications, map = Qualified.split qualified_map in
  let fields =
    Map.fold map ~init:Lowercase.Set.empty ~f:(fun ~key ~data:_ acc ->
      Set.add acc key)
  in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_records fields)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "record not in scope" (fields : Lowercase.Set.t)]
;;

let lookup_constructor qualified_constructor =
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_constructor in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_constructors name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error
      [%message "constructor not in scope" (name : Uppercase.t)]
;;

let lookup_field qualified_name =
  let%bind state = State.Result.get in
  let qualifications, name = Qualified.split qualified_name in
  let res =
    search_modules
      state.current_module_binding
      ~qualifications
      ~search_for:(fun module_bindings ->
        Map.find module_bindings.toplevel_fields name)
  in
  match res with
  | Some x -> State.Result.return x
  | None ->
    State.Result.error [%message "field not in scope" (name : Lowercase.t)]
;;

let absolute_name ~state ~name =
  let rec inner curr l =
    match l with
    | [] -> curr
    | (u, _) :: rest -> inner (Qualified.Qualified (u, curr)) rest
  in
  let { current_name; previous_modules } = state.module_history in
  let init =
    match current_name with
    | "" -> Qualified.Unqualified name
    | _ -> Qualified.Qualified (current_name, Qualified.Unqualified name)
  in
  inner init previous_modules
;;

let set_ordering (mono : mono) ~ordering =
  match mono with
  | Named p -> Named { p with ordering = Some ordering }
  | _ -> mono
;;

let open_module (qualifications : Qualified.qualifications) =
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let%bind module_bindings = find_module_binding qualifications in
  let current_module_binding =
    { current_module_binding with
      opened_modules = module_bindings :: current_module_binding.opened_modules
    }
  in
  State.Result.put { state with current_module_binding }
;;

let pop_opened_module =
  let%bind ({ current_module_binding; _ } as state) = State.Result.get in
  let opened_modules =
    match current_module_binding.opened_modules with
    | [] -> []
    | _ :: xs -> xs
  in
  let current_module_binding = { current_module_binding with opened_modules } in
  State.Result.put { state with current_module_binding }
;;

let change_to_module name module_bindings =
  let%bind ({ current_module_binding = old_module_binding; _ } as state) =
    State.Result.get
  in
  let { current_name; previous_modules } = state.module_history in
  let module_history =
    { current_name = name
    ; previous_modules = (current_name, old_module_binding) :: previous_modules
    }
  in
  let current_module_binding =
    { module_bindings with
      opened_modules = old_module_binding :: old_module_binding.opened_modules
    }
  in
  State.Result.put
    { state with
      current_module_binding
    ; module_history
    ; current_path = module_bindings.path
    }
;;

let change_to_new_module name =
  let%bind.State.Result state = State.Result.get in
  change_to_module
    name
    (empty_module_bindings (Module_path.append state.current_path name))
;;

let pop_module : (string * Typed_ast.module_) state_result_m =
  let%bind state = State.Result.get in
  let old_module_binding = state.current_module_binding in
  let { current_name; previous_modules } = state.module_history in
  let current_module_binding, module_history, current_path =
    match previous_modules with
    | [] ->
      ( empty_module_bindings state.current_path
      , { current_name; previous_modules = [] }
      , state.current_path )
    | (name, current_module_binding) :: xs ->
      ( current_module_binding
      , { current_name = name; previous_modules = xs }
      , Module_path.pop state.current_path )
  in
  let%map () =
    State.Result.put
      { state with current_module_binding; module_history; current_path }
  in
  current_name, old_module_binding
;;

let pop_module_and_add ~module_bindings =
  let%bind.State.Result current_name, _ = pop_module in
  add_module ~name:current_name ~module_bindings
;;

let pop_module_and_add_current =
  let%bind state = State.Result.get in
  pop_module_and_add ~module_bindings:state.current_module_binding
;;

let rec map_abstract_anys_m
  (abstract : Mem_rep.abstract)
  ~(f : string -> Mem_rep.abstract state_result_m)
  =
  let open Mem_rep in
  match abstract with
  | Any s -> f s
  | Closed `Bits8
  | Closed `Bits16
  | Closed `Bits64
  | Closed `Bits0
  | Closed `Bits32
  | Closed `Reg -> return abstract
  | Closed (`Struct l) ->
    let%map l = State.Result.all @@ List.map l ~f:(map_abstract_anys_m ~f) in
    Closed (`Struct l)
  | Closed (`Union l) ->
    let%map l = State.Result.all @@ List.map l ~f:(map_abstract_anys_m ~f) in
    Closed (`Union l)
;;

let rec map_abstract_anys
  (abstract : Mem_rep.abstract)
  ~(f : string -> Mem_rep.abstract)
  =
  let open Mem_rep in
  match abstract with
  | Any s -> f s
  | Closed `Bits8
  | Closed `Bits16
  | Closed `Bits64
  | Closed `Bits0
  | Closed `Bits32
  | Closed `Reg -> abstract
  | Closed (`Struct l) ->
    let l = List.map l ~f:(map_abstract_anys ~f) in
    Closed (`Struct l)
  | Closed (`Union l) ->
    let l = List.map l ~f:(map_abstract_anys ~f) in
    Closed (`Union l)
;;
