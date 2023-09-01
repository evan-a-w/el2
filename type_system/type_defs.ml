open! Core
open! Shared
open! Frontend
open! Ty
open! Inference_state
open! Monos

let constructor_arg_free_ty_vars constructor_arg =
  match constructor_arg with
  | Tuple_arg l -> snd @@ List.unzip l
  | Single_arg (_, x) -> [ x ]
;;

let ordering constructor_arg =
  Option.map constructor_arg ~f:constructor_arg_free_ty_vars
  |> Option.value ~default:[]
;;

let tyvar_map ordering =
  List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc tyvar ->
    Map.add_exn acc ~key:tyvar ~data:(TyVar tyvar))
;;

let rec type_of_type_expr type_expr : mono state_result_m =
  let open State.Result.Let_syntax in
  match type_expr with
  | Ast.Type_expr.Pointer type_expr ->
    let%map mono = type_of_type_expr type_expr in
    Reference mono
  | Ast.Type_expr.Tuple l ->
    let%map monos = State.Result.all (List.map l ~f:type_of_type_expr) in
    Tuple monos
  | Arrow (first, second) ->
    let%map first = type_of_type_expr first
    and second = type_of_type_expr second in
    Function (first, second)
  | Closure (a, v, b) ->
    let%map first = type_of_type_expr a
    and second = type_of_type_expr b in
    Closure
      ( first
      , second
      , { closure_mem_rep = Mem_rep.Any v; closed_args = []; closed_vars = [] }
      )
  | Ast.Type_expr.Single name -> lookup_type name
  | Ast.Type_expr.Multi (first, second) ->
    let%bind constructor_arg, _, type_proof = lookup_type_constructor second in
    let%bind arg = type_of_type_expr first in
    let vars =
      match constructor_arg with
      | None -> []
      | Some (Single_arg (_, x)) -> [ x ]
      | Some (Tuple_arg l) -> List.unzip l |> snd
    in
    let arg_list =
      match arg with
      | Tuple l -> l
      | _ -> [ arg ]
    in
    let%bind zipped =
      match List.zip vars arg_list with
      | Ok x -> return x
      | Unequal_lengths ->
        State.Result.error
          [%message
            "type constructor expected more args"
              ~constructor:(second : string Qualified.t)
              ~got:(List.length arg_list : int)
              ~expected:(List.length vars : int)]
    in
    let%map replacement_map =
      match Lowercase.Map.of_alist zipped with
      | `Ok x -> return x
      | `Duplicate_key x ->
        State.Result.error
          [%message
            "duplicate arg in type constructor"
              ~constructor:(second : string Qualified.t)
              (x : Lowercase.t)]
    in
    Named (replace_ty_vars_type_proof ~replacement_map type_proof)
;;

let type_proof_of_monos
  ~type_name
  ~absolute_type_name
  ~ordering
  monos
  type_id
  ~mem_rep
  =
  let free_var_set =
    List.fold monos ~init:Lowercase.Set.empty ~f:(fun acc mono ->
      Set.union acc (free_ty_vars mono))
  in
  let tyvar_map =
    Set.fold free_var_set ~init:Lowercase.Map.empty ~f:(fun acc x ->
      Map.add_exn acc ~key:x ~data:(TyVar x))
  in
  { type_name; absolute_type_name; tyvar_map; ordering; type_id; mem_rep }
;;

let type_of_type_def_lit
  ~(type_name : string)
  ~type_id
  ~ordering
  (type_def_lit : Ast.Type_def_lit.t)
  =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  let absolute_type_name = absolute_name ~state ~name:type_name in
  match type_def_lit with
  | Ast.Type_def_lit.Type_expr type_expr ->
    let%map mono = type_of_type_expr type_expr in
    let mem_rep = mem_rep_of_mono mono in
    let type_proof =
      { type_name
      ; absolute_type_name
      ; tyvar_map =
          free_ty_vars mono
          |> Set.fold ~init:Lowercase.Map.empty ~f:(fun acc x ->
            Map.add_exn ~key:x ~data:(TyVar x) acc)
      ; ordering
      ; type_id
      ; mem_rep
      }
    in
    type_proof, User_mono mono
  | Ast.Type_def_lit.Record l ->
    let%bind record_type =
      List.map l ~f:(fun (name, (type_expr, mutability)) ->
        let%map mono = type_of_type_expr type_expr in
        name, (mono, mutability))
      |> State.Result.all
    in
    let mem_rep = mem_rep_of_user_type (Record record_type) in
    let type_proof =
      type_proof_of_monos
        ~type_name
        ~absolute_type_name
        ~ordering
        ~mem_rep
        (List.map record_type ~f:(Fn.compose fst snd))
        type_id
    in
    let user_type = Record record_type in
    let%bind polys =
      State.Result.all
        (List.map record_type ~f:(fun (field, (mono, mut)) ->
           let%map.State poly = gen mono in
           Ok (field, (poly, mut))))
    in
    let field_map = Lowercase.Map.of_alist_exn polys in
    let%map () = add_record field_map type_proof in
    type_proof, user_type
  | Ast.Type_def_lit.Enum l ->
    let%bind enum_type =
      List.map l ~f:(fun (name, type_expr) ->
        let%map mono =
          match type_expr with
          | Some type_expr -> type_of_type_expr type_expr >>| Option.some
          | None -> return None
        in
        name, mono)
      |> State.Result.all
    in
    let mem_rep = mem_rep_of_user_type (Enum enum_type) in
    let monos = List.filter_map enum_type ~f:(fun (_, mono) -> mono) in
    let type_proof =
      type_proof_of_monos
        ~type_name
        ~absolute_type_name
        ~ordering
        monos
        type_id
        ~mem_rep
    in
    let user_type = Enum enum_type in
    let%map () =
      State.Result.all_unit
      @@ List.map enum_type ~f:(fun (x, mono_option) ->
        let%bind poly_option =
          match mono_option with
          | Some mono -> State.map (gen mono) ~f:(fun x -> Ok (Some x))
          | None -> return None
        in
        add_constructor x poly_option type_proof)
    in
    type_proof, user_type
;;

let type_type_def
  ({ type_name = type_binding; type_def; ast_tags = _ } :
    Ast.Type_def_lit.t Ast.type_description)
  =
  let open State.Result.Let_syntax in
  let%bind state = State.Result.get in
  match type_binding with
  | Ast.Type_binding.Mono type_name ->
    let absolute_type_name = absolute_name ~state ~name:type_name in
    let type_id = type_id_of_absolute_name absolute_type_name in
    let%bind type_proof, user_type =
      type_of_type_def_lit ~type_name ~type_id ~ordering:None type_def
    in
    let%map () =
      match Map.length type_proof.tyvar_map with
      | 0 -> add_type type_name user_type type_proof
      | _ ->
        State.Result.error
          [%message
            "type definition has free type variables"
              (user_type : user_type)
              ~vars:
                (Map.to_alist type_proof.tyvar_map |> List.map ~f:fst
                  : Lowercase.t list)
              (type_name : Lowercase.t)]
    in
    Typed_ast.(
      Type_def Type_def.{ type_binding; type_def = user_type; type_proof })
  | Ast.Type_binding.Poly (arg, type_name) ->
    let absolute_type_name = absolute_name ~state ~name:type_name in
    let type_id = type_id_of_absolute_name absolute_type_name in
    let constructor_arg =
      match arg with
      | Ast.Type_binding.Single (v, l) -> Some (Single_arg (v, l))
      | Ast.Type_binding.Tuple l -> Some (Tuple_arg l)
    in
    let ordering = ordering constructor_arg in
    let lhs_ty_vars =
      List.fold ordering ~init:Lowercase.Map.empty ~f:(fun acc key ->
        Map.add_exn acc ~key ~data:(TyVar key))
    in
    let mem_rep = Mem_rep.Any "0" in
    let type_proof =
      { type_name
      ; absolute_type_name
      ; ordering = Some ordering
      ; type_id
      ; tyvar_map = lhs_ty_vars
      ; mem_rep
      }
    in
    let%bind () =
      add_type_constructor
        constructor_arg
        type_name
        (Abstract mem_rep)
        type_proof
    in
    let%bind type_proof', user_type =
      type_of_type_def_lit
        ~type_name
        ~type_id
        ~ordering:(Some ordering)
        type_def
    in
    let rhs_ty_vars = Map.key_set type_proof'.tyvar_map |> Obj.magic in
    let lhs_ty_vars = Map.key_set lhs_ty_vars |> Obj.magic in
    let%map () =
      match Lowercase.Set.equal lhs_ty_vars rhs_ty_vars with
      | true ->
        set_type_constructor constructor_arg type_name user_type type_proof
      | false ->
        State.Result.error
          [%message
            "Type vars not equal in type def"
              (type_name : Lowercase.t)
              (type_proof : type_proof)
              (lhs_ty_vars : Lowercase.Set.t)
              (rhs_ty_vars : Lowercase.Set.t)]
    in
    Typed_ast.(
      Type_def Type_def.{ type_binding; type_def = user_type; type_proof })
;;
