open! Core
open! Shared
open! Frontend
open! Ty
open! Inference_state
open! Type_defs
open! Monos
open! Unify
open! State.Result.Let_syntax

let rec value_restriction expr =
  match expr with
  | Ast.Lambda _ -> false
  | Ast.Node n -> value_restriction_node n
  | Ast.If (a, b, c) -> List.exists ~f:value_restriction [ a; b; c ]
  | Ast.App (_, _) -> true
  | Ast.Let_in (Ast.Nonrec (_, b), c) ->
    List.exists ~f:value_restriction [ b; c ]
  | Ast.Let_in (Ast.Rec l, c) ->
    List.exists ~f:value_restriction (c :: List.map l ~f:snd)
  | Ast.Match (_, _) -> true
  | Ast.Typed (e, _) -> value_restriction e
  | _ -> true

and value_restriction_node node =
  match node with
  | Ast.Var _ -> false
  | Ast.Literal _ -> false
  | Ast.Tuple qualified ->
    let _, l = Qualified.split qualified in
    List.exists ~f:value_restriction l
  | Ast.Constructor _ -> true
  | Ast.Record qualified ->
    let _, l = Qualified.split qualified in
    Map.exists ~f:value_restriction l
  | Ast.Wrapped qualified ->
    let _, l = Qualified.split qualified in
    value_restriction l
;;

let type_literal literal =
  State.Result.return @@ Typed_ast.expr_of_literal literal
;;

type add_var_t = ?binding_id:type_id -> string -> poly -> unit state_result_m

let rec gen_binding_ty_vars
  ~initial_vars
  ~(binding : Ast.Binding.t)
  ~(add_var : add_var_t)
  : (mono * Lowercase.t list) state_result_m
  =
  match binding with
  | Ast.Binding.Literal l ->
    let mono = Typed_ast.Literal.mono_of_t l in
    return (mono, initial_vars)
  | Ast.Binding.Name var ->
    let%bind ty_var = gen_ty_var in
    let poly = Mono ty_var in
    let%map () = add_var var poly in
    ty_var, var :: initial_vars
  | Ast.Binding.Constructor (constructor, rest) ->
    let%bind mono_arg, mono_res = inst_constructor constructor in
    (match rest, mono_arg with
     | None, None -> return (mono_res, [])
     | None, Some mono_arg ->
       State.Result.error
         [%message
           "Constructor takes an argument (none given)"
             (constructor : Uppercase.t Qualified.t)
             (mono_arg : mono)]
     | Some given, None ->
       State.Result.error
         [%message "Constructor takes no argument" (given : Ast.Binding.t)]
     | Some binding, Some mono_arg ->
       let%bind mono, vars =
         gen_binding_ty_vars ~initial_vars ~binding ~add_var
       in
       let%map () = unify mono_arg mono in
       mono_res, vars)
  | Ast.Binding.Typed (binding, value_tag) ->
    let type_expr = value_tag.Ast.Value_tag.type_expr in
    (match type_expr with
     | None -> gen_binding_ty_vars ~initial_vars ~binding ~add_var
     | Some type_expr ->
       let%bind tagged_mono = type_of_type_expr type_expr in
       let%bind mono, vars =
         gen_binding_ty_vars ~initial_vars ~binding ~add_var
       in
       let%map () = unify tagged_mono mono in
       mono, vars)
  | Ast.Binding.Pointer binding ->
    let%map mono, vars = gen_binding_ty_vars ~initial_vars ~binding ~add_var in
    Reference mono, vars
  | Ast.Binding.Renamed (binding, var) ->
    let%bind mono, vars = gen_binding_ty_vars ~initial_vars ~binding ~add_var in
    let%map () = add_var var (Mono mono) in
    mono, var :: vars
  | Ast.Binding.Tuple qualified ->
    let qualifications, tuple = Qualified.split qualified in
    let%bind () = open_module qualifications in
    let%bind processed_list =
      State.Result.all
        (List.map tuple ~f:(fun binding ->
           gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var))
    in
    let monos, vars_list = List.unzip processed_list in
    let vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    Tuple monos, List.concat [ vars; initial_vars ]
  | Ast.Binding.Record qualified_map ->
    let qualifications, record = Qualified.split qualified_map in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof = lookup_record qualified_map in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_searched = Named type_proof in
    let%bind field_map =
      try
        return
        @@ Map.merge record field_map ~f:(fun ~key -> function
          | `Both x -> Some x
          | `Left _ -> raise (Field_left_only key)
          | `Right _ -> raise (Field_right_only key))
      with
      | Field_left_only key ->
        State.Result.error
          [%message
            "Field in pattern is not present in type" (key : Lowercase.t)]
      | Field_right_only key ->
        State.Result.error
          [%message "Field is not present in pattern" (key : Lowercase.t)]
    in
    let%bind vars_list =
      Map.fold
        field_map
        ~init:(State.Result.return [])
        ~f:(fun ~key:_ ~data:(binding, poly) acc ->
          let%bind vars_list = acc in
          let mono = mono_of_poly_no_inst poly in
          let%bind mono =
            map_ty_vars_m mono ~f:(fun (v, _) ->
              lookup_in_type_proof mono_searched ~look_for:v)
          in
          let%bind mono', vars =
            gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var
          in
          let%map () = unify mono mono' in
          vars :: vars_list)
    in
    let res_vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    mono_searched, List.concat [ res_vars; initial_vars ]
;;

let gen_var var ~(add_var : add_var_t) ~pop_var =
  let%bind value, binding_id, _, _ = lookup_var (Qualified.Unqualified var) in
  let%bind () = pop_var var in
  let%bind mono = inst_result value in
  let%bind mono = apply_substs mono in
  let%bind poly = State.Result.t_of_state (gen mono) in
  add_var ~binding_id var poly
;;

let is_plain_function poly =
  let mono = mono_of_poly_no_inst poly in
  match%map.State.Result reach_end_mono mono with
  | Function (_, _) | Closure (_, _, { closed_vars = []; closed_args = []; _ })
    -> true
  | Weak _ | TyVar _ | Tuple _ | Reference _ | Named _ | Closure (_, _, _) ->
    false
;;

let rec already_bound
  ?(acc = [])
  ?(shadowed = Lowercase.Set.empty)
  (expr : Ast.expr)
  =
  match expr with
  | Ast.Node n -> already_bound_node ~acc ~shadowed n
  | Ast.If (a, b, c) ->
    let%bind acc = already_bound ~acc ~shadowed a in
    let%bind acc = already_bound ~acc ~shadowed b in
    already_bound ~acc ~shadowed c
  | Ast.Lambda (binding, expr) ->
    let shadowed = add_shadowed ~shadowed ~binding in
    already_bound ~acc ~shadowed expr
  | Ast.App (a, b) ->
    let%bind acc = already_bound ~acc ~shadowed a in
    already_bound ~acc ~shadowed b
  | Ast.Let_in (Nonrec (binding, expr1), expr2) ->
    let%bind acc = already_bound ~acc ~shadowed expr1 in
    let shadowed = add_shadowed ~shadowed ~binding in
    already_bound ~acc ~shadowed expr2
  | Ast.Let_in (Rec l, expr2) ->
    let%bind shadowed =
      List.fold l ~init:(return shadowed) ~f:(fun acc (binding, _) ->
        let%map shadowed = acc in
        add_shadowed ~shadowed ~binding)
    in
    let%bind acc =
      List.fold l ~init:(return acc) ~f:(fun acc (_, expr) ->
        let%bind acc = acc in
        already_bound ~acc ~shadowed expr)
    in
    already_bound ~acc ~shadowed expr2
  | Ast.Ref expr
  | Ast.Typed (expr, _)
  | Ast.Deref expr
  | Ast.Field_access (expr, _) -> already_bound ~acc ~shadowed expr
  | Ast.Field_set (expr1, _, expr2) ->
    let%bind acc = already_bound ~acc ~shadowed expr1 in
    already_bound ~acc ~shadowed expr2
  | Ast.Match (expr, cases) ->
    let%bind acc = already_bound ~acc ~shadowed expr in
    List.fold
      cases
      ~init:(State.Result.return acc)
      ~f:(fun acc (binding, expr) ->
        let%bind acc = acc in
        let shadowed = add_shadowed ~shadowed ~binding in
        already_bound ~acc ~shadowed expr)

and already_bound_node ~acc ~shadowed (node : Ast.node) =
  match node with
  | Ast.Var (Qualified.Unqualified s) ->
    let is_shadowed = Set.mem shadowed s in
    (match%bind lookup_local_var s with
     | Some (poly, binding_id, `Not, arg) when not is_shadowed ->
       (match%map is_plain_function poly with
        | true -> acc
        | false -> (binding_id, arg) :: acc)
     | _ -> return acc)
  | Ast.Var _ | Ast.Literal _ | Ast.Constructor _ -> return acc
  | Ast.Tuple l ->
    let l = Qualified.inner l in
    List.fold l ~init:(return acc) ~f:(fun acc expr ->
      let%bind acc = acc in
      already_bound ~acc ~shadowed expr)
  | Ast.Record r ->
    let r = Qualified.inner r in
    Map.fold r ~init:(return acc) ~f:(fun ~key:_ ~data:expr acc ->
      let%bind acc = acc in
      already_bound ~acc ~shadowed expr)
  | Ast.Wrapped e ->
    let e = Qualified.inner e in
    already_bound ~acc ~shadowed e

and add_shadowed ~shadowed ~binding =
  let res = ref shadowed in
  Ast.Binding.iter_names ~f:(fun name -> res := Set.add !res name) binding;
  !res
;;

let rec type_node node =
  match node with
  | Ast.Literal literal -> type_literal literal
  | Ast.Var var_name ->
    let%bind poly, binding_id, _, _ = lookup_var var_name in
    let%map mono = inst_result poly in
    Typed_ast.(Node (Var (var_name, binding_id))), mono
  | Ast.Tuple qualified_tuple ->
    let qualifications, tuple = Qualified.split qualified_tuple in
    let%bind () = open_module qualifications in
    let%bind l = State.Result.all (List.map tuple ~f:type_expr) in
    let monos = List.map l ~f:snd in
    let%map () = pop_opened_module in
    let l = Qualified.prepend ~qualifications (Unqualified l) in
    Typed_ast.(Node (Tuple l)), Tuple monos
  | Ast.Wrapped qualified_expr ->
    let qualifications, expr = Qualified.split qualified_expr in
    let%bind () = open_module qualifications in
    let%bind ((_, mono) as expr) = type_expr expr in
    let%map () = pop_opened_module in
    let expr = Qualified.prepend ~qualifications (Unqualified expr) in
    Typed_ast.(Node (Wrapped expr)), mono
  | Ast.Constructor constructor ->
    let%map mono = type_of_constructor constructor in
    Typed_ast.(Node (Constructor constructor)), mono
  | Ast.Record qualified_record ->
    let qualifications, record = Qualified.split qualified_record in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof =
      lookup_record (Qualified.Unqualified record)
    in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_res = Named type_proof in
    let field_list = Map.to_alist field_map in
    (* lookup the tyvar in the map thingo in mono_res *)
    let%bind field_mono_map =
      List.map field_list ~f:(fun (field, poly) ->
        let mono = mono_of_poly_no_inst poly in
        let%map mono =
          map_ty_vars_m mono ~f:(fun (v, _) ->
            lookup_in_type_proof mono_res ~look_for:v)
        in
        field, mono)
      |> State.Result.all
      >>| Lowercase.Map.of_alist_exn
    in
    let%bind expr_map =
      Map.fold
        record
        ~init:(State.Result.return Lowercase.Map.empty)
        ~f:(fun ~key:field ~data:expr acc ->
          let%bind acc = acc in
          let%bind ((_, mono) as expr) = type_expr expr in
          let%map () =
            match Map.find field_mono_map field with
            | None ->
              State.Result.error
                [%message "Unknown field" (field : Lowercase.t)]
            | Some field_mono -> unify field_mono mono
          in
          Map.set acc ~key:field ~data:expr)
    in
    let expr_map = Qualified.prepend ~qualifications (Unqualified expr_map) in
    let%map mono = apply_substs mono_res in
    Typed_ast.(Node (Record expr_map)), mono

and add_module_var_mono ~generalize ~value_restriction var mono =
  let%bind poly = poly_of_mono ~generalize ~value_restriction mono in
  add_module_var var poly

and add_local_var_mono ~is_rec ~is_arg ~generalize ~value_restriction var mono =
  let%bind poly = poly_of_mono ~generalize ~value_restriction mono in
  add_local_var ~is_rec ~is_arg var poly

and type_binding ~act_on_var ~initial_vars ~(binding : Ast.Binding.t) ~mono =
  match binding with
  | Ast.Binding.Literal l ->
    let%bind _, binding_mono = type_literal l in
    let%map () = unify binding_mono mono in
    Typed_ast.Literal_binding l, mono, initial_vars
  | Ast.Binding.Name var ->
    (* let%bind poly = poly_of_mono ~generalize ~value_restriction mono in *)
    (* let%map () = act_on_var var poly in *)
    let%map () = act_on_var var mono in
    Typed_ast.Name_binding var, mono, var :: initial_vars
  | Ast.Binding.Constructor (constructor, rest) ->
    let%bind mono_arg, mono_res = inst_constructor constructor in
    (match rest, mono_arg with
     | None, None ->
       return (Typed_ast.Constructor_binding (constructor, None), mono_res, [])
     | None, Some mono_arg ->
       State.Result.error
         [%message
           "Constructor takes an argument (none given)"
             (constructor : Uppercase.t Qualified.t)
             (mono_arg : mono)]
     | Some given, None ->
       State.Result.error
         [%message
           "Constructor takes no argument"
             (constructor : Uppercase.t Qualified.t)
             (given : Ast.Binding.t)]
     | Some binding, Some mono_arg ->
       let%bind inner, _, vars =
         type_binding ~act_on_var ~initial_vars ~binding ~mono:mono_arg
       in
       let%map () = unify mono_res mono in
       Typed_ast.Constructor_binding (constructor, Some inner), mono_res, vars)
  | Ast.Binding.Typed (binding, value_tag) ->
    let type_expr = value_tag.Ast.Value_tag.type_expr in
    (match type_expr with
     | None -> type_binding ~act_on_var ~initial_vars ~binding ~mono
     | Some type_expr ->
       let%bind tagged_mono = type_of_type_expr type_expr in
       let%bind () = unify tagged_mono mono in
       let%bind res, mono_res, vars =
         type_binding ~act_on_var ~initial_vars ~binding ~mono
       in
       let%map () = unify mono_res tagged_mono in
       res, mono, vars)
  | Ast.Binding.Renamed (binding, var) ->
    let%bind res, mono, vars =
      type_binding ~act_on_var ~initial_vars ~binding ~mono
    in
    let%map () = act_on_var var mono in
    Typed_ast.Renamed_binding (res, var), mono, var :: vars
  | Ast.Binding.Pointer binding ->
    let%bind ty_var = gen_ty_var in
    let%bind () = unify (Reference ty_var) mono in
    let%map inner, mono, vars =
      type_binding ~act_on_var ~initial_vars ~binding ~mono:ty_var
    in
    Typed_ast.Reference_binding inner, mono, vars
  | Ast.Binding.Tuple qualified ->
    let qualifications, tuple = Qualified.split qualified in
    let%bind () = open_module qualifications in
    let%bind arg_monos =
      match mono with
      | Tuple list ->
        if List.length list <> List.length tuple
        then
          State.Result.error
            [%message
              "Tuple length mismatch" (mono : mono) (tuple : Ast.Binding.t list)]
        else State.Result.return list
      | _ -> State.Result.error [%message "Expected tuple" (mono : mono)]
    in
    let tuple_zipped = List.zip_exn tuple arg_monos in
    let%bind processed_list =
      State.Result.all
        (List.map tuple_zipped ~f:(fun (binding, mono) ->
           type_binding ~act_on_var ~initial_vars:[] ~binding ~mono))
    in
    let bindings, monos, vars_list = List.unzip3 processed_list in
    let bindings = Qualified.prepend ~qualifications (Unqualified bindings) in
    let vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    ( Typed_ast.Tuple_binding bindings
    , Tuple monos
    , List.concat [ vars; initial_vars ] )
  | Ast.Binding.Record qualified_map ->
    let qualifications, record = Qualified.split qualified_map in
    let%bind () = open_module qualifications in
    let%bind field_map, type_proof = lookup_record qualified_map in
    let%bind type_proof = inst_type_proof type_proof in
    let mono_searched = Named type_proof in
    let%bind () = unify mono_searched mono in
    let%bind field_map =
      try
        return
        @@ Map.merge record field_map ~f:(fun ~key -> function
          | `Both x -> Some x
          | `Left _ -> raise (Field_left_only key)
          | `Right _ -> raise (Field_right_only key))
      with
      | Field_left_only key ->
        State.Result.error
          [%message
            "Field in pattern is not present in type" (key : Lowercase.t)]
      | Field_right_only key ->
        State.Result.error
          [%message "Field is not present in pattern" (key : Lowercase.t)]
    in
    let%bind inner_map, vars_list =
      Map.fold
        field_map
        ~init:(State.Result.return (Lowercase.Map.empty, []))
        ~f:(fun ~key ~data:(binding, poly) acc ->
          let%bind inner_map, vars_list = acc in
          let mono = mono_of_poly_no_inst poly in
          let%bind mono =
            map_ty_vars_m mono ~f:(fun (v, _) ->
              lookup_in_type_proof mono_searched ~look_for:v)
          in
          let%bind inner, mono', vars =
            type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
          in
          let%map () = unify mono' mono in
          let inner_map = Map.set inner_map ~key ~data:inner in
          inner_map, vars :: vars_list)
    in
    let inner_map = Qualified.prepend ~qualifications (Unqualified inner_map) in
    let res_vars = List.concat (List.rev vars_list) in
    let%map () = pop_opened_module in
    ( Typed_ast.Record_binding inner_map
    , mono_searched
    , List.concat [ res_vars; initial_vars ] )

and let_each_of_binding_typed
  ~(binding : Ast.Binding.t)
  ~mono1
  ~expr2
  ~generalize
  ~value_restriction
  ~add_var_mono
  ~pop_var
  =
  let act_on_var = add_var_mono ~generalize ~value_restriction in
  let%bind binding, mono, vars =
    type_binding ~act_on_var ~initial_vars:[] ~binding ~mono:mono1
  in
  let%bind () = unify mono mono1 in
  let%bind res = type_expr expr2 in
  let%map () = State.Result.all_unit (List.map vars ~f:pop_var) in
  binding, res

and mono_of_binding
  ~(binding : Ast.Binding.t)
  ~expr1
  ~expr2
  ~generalize
  ~add_var_mono
  ~pop_var
  =
  let value_restriction = value_restriction expr1 in
  let%bind inner, mono1 = type_expr expr1 in
  let%bind mono1 = apply_substs mono1 in
  let%map binding, mono =
    let_each_of_binding_typed
      ~binding
      ~mono1
      ~expr2
      ~generalize
      ~value_restriction
      ~add_var_mono
      ~pop_var
  in
  binding, (inner, mono)

and add_nonrec_bindings ~binding ~expr ~add_var_mono =
  let value_restriction = value_restriction expr in
  let%bind inner, mono = type_expr expr in
  let%bind mono = apply_substs mono in
  let act_on_var = add_var_mono ~generalize:true ~value_restriction in
  let%bind binding, mono', vars =
    type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
  in
  let%map () = unify mono mono' in
  binding, (inner, mono), vars

and check_rec_rhs expr =
  match expr with
  | Ast.Lambda _ -> State.Result.return ()
  | _ ->
    State.Result.error
      [%message
        "Only functions are allowed in rec bindings" ~got:(expr : Ast.expr)]

and add_rec_bindings l ~(add_var : add_var_t) ~pop_var =
  let%bind bindings =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
         let%bind () = check_rec_rhs expr in
         let%map _, b =
           gen_binding_ty_vars ~initial_vars:[] ~binding ~add_var
         in
         b, value_restriction expr))
  in
  let act_on_var var mono =
    let%bind current, _, _, _ = lookup_var (Qualified.Unqualified var) in
    let mono' = mono_of_poly_no_inst current in
    let%bind () = unify mono mono' in
    add_var var (Mono mono)
  in
  let%bind vars_list =
    State.Result.all
      (List.map l ~f:(fun (binding, expr) ->
         let%bind inner, mono = type_expr expr in
         let%map binding, mono, vars =
           type_binding ~act_on_var ~initial_vars:[] ~binding ~mono
         in
         binding, (inner, mono), vars))
  in
  let typed_bindings, exprs, vars_list = List.unzip3 vars_list in
  let%map () =
    List.map bindings ~f:(fun (inner, v) ->
      match v with
      | false ->
        State.Result.all_unit (List.map inner ~f:(gen_var ~add_var ~pop_var))
      | true -> return ())
    |> State.Result.all_unit
  in
  let bindings = List.unzip bindings |> fst in
  typed_bindings, exprs, List.concat [ vars_list; bindings ]

and type_field expr field ~mut =
  let%bind type_proof, muta, poly = lookup_field field in
  let%bind () =
    match mut, muta with
    | true, `Immutable ->
      State.Result.error
        [%message "Field needs to be mutable" (field : Lowercase.t Qualified.t)]
    | _ -> return ()
  in
  let%bind named_poly = Named type_proof |> gen |> State.map ~f:Result.return in
  let%bind monos =
    inst_many [ named_poly; poly ] |> State.map ~f:Result.return
  in
  let type_proof, mono =
    match monos with
    | [ Named type_proof; mono ] -> type_proof, mono
    | _ -> assert false
  in
  let%bind inner, expr_mono = type_expr expr in
  let%bind () = unify expr_mono (Named type_proof) in
  let%map mono = apply_substs mono in
  (* result type, (expr for the LHS)*)
  mono, (inner, expr_mono)

and type_expr expr =
  match expr with
  | Ast.Node node -> type_node node >>= substitute
  | Ref expr ->
    let%bind inner, mono = type_expr expr in
    let%map mono = apply_substs mono in
    Typed_ast.Ref (inner, mono), Reference mono
  | Deref expr ->
    let%bind tyvar = gen_ty_var in
    let%bind inner, inner_mono = type_expr expr in
    let%bind () = unify inner_mono (Reference tyvar) in
    let%map mono = apply_substs tyvar in
    Typed_ast.Deref (inner, inner_mono), mono
  | Field_access (expr, field) ->
    let%bind mono, lhs_expr = type_field expr field ~mut:false in
    (Typed_ast.Field_access (lhs_expr, field), mono) |> substitute
  | Field_set (expr1, field, expr2) ->
    let%bind field_mono, lhs_expr = type_field expr1 field ~mut:true in
    let%bind ((_, rhs_mono) as rhs_expr) = type_expr expr2 in
    let%bind () = unify field_mono rhs_mono in
    (Typed_ast.Field_set (lhs_expr, field, rhs_expr), Named unit_type)
    |> substitute
  | If (pred, then_, else_) ->
    let%bind ((_, pred_mono) as pred_expr) = type_expr pred in
    let%bind ((_, then_mono) as then_expr) = type_expr then_ in
    let%bind ((_, else_mono) as else_expr) = type_expr else_ in
    let%bind () = unify pred_mono (Named bool_type) in
    let%bind () = unify then_mono else_mono in
    let%map then_mono = apply_substs then_mono in
    Typed_ast.If (pred_expr, then_expr, else_expr), then_mono
  | App (func, arg) ->
    let%bind ((_, func_mono) as func_expr) = type_expr func in
    let%bind ((_, arg_mono) as arg_expr) = type_expr arg in
    let%bind res_mono = gen_ty_var in
    let%bind sym = State.map ~f:Result.return gensym in
    let%bind () =
      unify
        func_mono
        (Closure
           ( arg_mono
           , res_mono
           , { closure_mem_rep = Mem_rep.Any sym
             ; closed_vars = []
             ; closed_args = []
             } ))
    in
    let%bind res_mono = apply_substs res_mono in
    (Typed_ast.App (func_expr, arg_expr), res_mono) |> substitute
  | Typed (expr, ty) ->
    let%bind expr_inner, mono = type_expr expr in
    let%map mono =
      match ty.type_expr with
      | None -> apply_substs mono
      | Some ty ->
        let%bind ty_mono = type_of_type_expr ty in
        let%bind () = unify mono ty_mono in
        apply_substs mono
    in
    expr_inner, mono
  | Let_in (Ast.Nonrec (binding, expr1), expr2) ->
    let%bind binding, expr, vars =
      add_nonrec_bindings
        ~binding
        ~expr:expr1
        ~add_var_mono:(add_local_var_mono ~is_rec:false ~is_arg:false)
    in
    let%bind ((_, res_mono) as res_expr) = type_expr expr2 in
    let%bind () = State.Result.all_unit (List.map vars ~f:pop_local_var) in
    let%map res_mono = apply_substs res_mono in
    Typed_ast.(Let_in (Nonrec (binding, expr), res_expr)), res_mono
  | Let_in (Ast.Rec l, expr2) ->
    let%bind bindings, exprs, vars =
      add_rec_bindings
        ~add_var:(add_local_var ~is_rec:true ~is_arg:false)
        ~pop_var:pop_local_var
        l
    in
    let let_each_list = List.zip_exn bindings exprs in
    let%bind ((_, res_mono) as res_expr) = type_expr expr2 in
    let%bind () =
      State.Result.all_unit
        (List.map vars ~f:(fun vars ->
           State.Result.all_unit (List.map (List.rev vars) ~f:pop_local_var)))
    in
    let%map res_mono = apply_substs res_mono in
    Typed_ast.(Let_in (Rec let_each_list, res_expr)), res_mono
  | Match (expr1, cases) ->
    let%bind ((_, mono1) as expr1) = type_expr expr1 in
    let%bind cases =
      State.Result.all
        (List.map cases ~f:(fun (binding, expr2) ->
           let_each_of_binding_typed
             ~binding
             ~mono1
             ~expr2
             ~generalize:false
             ~value_restriction:false
             ~add_var_mono:(add_local_var_mono ~is_rec:false ~is_arg:false)
             ~pop_var:pop_local_var))
    in
    let%map mono =
      match cases with
      | [] -> State.Result.error [%message "Empty match"]
      | (_, (_, mono)) :: _ as l ->
        let%bind () =
          State.Result.all_unit
            (List.map l ~f:(fun (_, (_, mono')) -> unify mono mono'))
        in
        apply_substs mono
    in
    Typed_ast.(Match (expr1, cases)), mono
  | Lambda (binding, body) ->
    let%bind var = gen_ty_var in
    let%bind binding, (res_inner, res_mono) =
      let_each_of_binding_typed
        ~binding
        ~mono1:var
        ~expr2:body
        ~generalize:false
        ~value_restriction:false
        ~add_var_mono:(add_local_var_mono ~is_rec:false ~is_arg:true)
        ~pop_var:pop_local_var
    in
    let%bind var = apply_substs var in
    let%bind closed = already_bound body in
    let%bind closed =
      State.Result.all
      @@ List.map closed ~f:(fun (binding_id, arg) ->
        let%map { poly; _ } = lookup_binding_id binding_id in
        let mono = get_mono_from_poly_without_gen poly in
        binding_id, arg, mono)
    in
    let closed_args, closed_vars =
      List.partition_map closed ~f:(fun (binding_id, arg, mono) ->
        match arg with
        | `Arg -> Either.First (binding_id, mono)
        | `Not -> Either.Second (binding_id, mono))
    in
    let closed_arg_mem_reps =
      List.map closed_args ~f:(fun (_, mono) -> mem_rep_of_mono mono)
    in
    let closed_var_mem_reps =
      List.map closed_vars ~f:(fun (_, mono) -> mem_rep_of_mono mono)
    in
    let joined_mem_reps = closed_var_mem_reps @ closed_arg_mem_reps in
    let closure_mem_rep =
      match joined_mem_reps with
      | [] -> Mem_rep.Closed `Bits0
      | [ x ] -> x
      | xs -> Mem_rep.Closed (`Struct xs)
    in
    let%map res_mono = apply_substs res_mono in
    (match List.is_empty closed_vars with
     | true ->
       ( Typed_ast.Lambda (binding, (res_inner, res_mono))
       , Function (var, res_mono) )
     | false ->
       ( Typed_ast.Lambda (binding, (res_inner, res_mono))
       , Closure (var, res_mono, { closed_vars; closed_args; closure_mem_rep })
       ))
;;

let type_let_def (let_def : Ast.let_def) =
  let%bind res =
    match let_def with
    | Ast.Rec l ->
      let%bind bindings, exprs, _ =
        add_rec_bindings l ~add_var:add_module_var ~pop_var:pop_module_var
      in
      let let_each_list = List.zip_exn bindings exprs in
      return @@ Typed_ast.Rec let_each_list
    | Ast.Nonrec (binding, expr) ->
      let%bind binding, expr, _ =
        add_nonrec_bindings ~binding ~expr ~add_var_mono:add_module_var_mono
      in
      return @@ Typed_ast.Nonrec (binding, expr)
  in
  let%bind state = State.Result.get in
  let%map () = State.Result.put { state with mono_ufds = Mono_ufds.empty } in
  res
;;

let rec process_module_named (name : Uppercase.t Qualified.t) =
  let qualifications = Qualified.full_qualifications name in
  let%bind module_bindings = find_module_binding qualifications in
  let module_bindings =
    { module_bindings with data = Typed_ast.There module_bindings }
  in
  set_current_module_binding module_bindings

and process_struct (toplevels : Ast.toplevel list) =
  let%bind toplevels =
    State.Result.all @@ List.map ~f:type_toplevel toplevels
  in
  let%bind state = State.Result.get in
  let current_module_binding =
    { state.current_module_binding with data = Typed_ast.Here toplevels }
  in
  State.Result.put { state with current_module_binding }

and process_functor_app (f : Uppercase.t Qualified.t) (a : Ast.module_def list) =
  let _ = f, a in
  failwith "TODO"

and type_sig (toplevel_types : Ast.module_sig) =
  State.Result.all @@ List.map ~f:type_toplevel_type toplevel_types

and process_module_def (d : Ast.module_def) =
  match d with
  | Ast.Struct s -> process_struct s
  | Ast.Named f -> process_module_named f
  | Ast.Functor_app (f, a) -> process_functor_app f a
  | Ast.Module_typed (s, si) ->
    let _ = s, si in
    failwith "TODO"
(* let open State.Result.Let_syntax in *)
(* let%bind signature = type_sig si in *)
(* let%bind () = process_module_def s in *)
(* let%bind name, definition = pop_module in *)
(* let%bind module_ = unify_module_bindings ~signature ~definition in *)
(* change_to_module name module_ *)

and type_module_description _ = failwith "TODO"

and type_module
  ~(module_description : Ast.module_sig option Ast.module_description)
  ~(module_def : Ast.module_def)
  =
  let%bind () = change_to_new_module module_description.module_name in
  match module_description with
  | { module_name; functor_args = []; module_sig } ->
    let%bind sig_module_bindings =
      match module_sig with
      | Some module_sig ->
        let%bind _ = type_sig module_sig in
        let%bind name, module_ = pop_module in
        let%map () = change_to_new_module name in
        Some module_
      | None -> return None
    in
    let%bind () = process_module_def module_def in
    let%bind current_name, def_module_bindings = pop_module in
    let%bind module_bindings =
      match sig_module_bindings with
      | Some sig_module_bindings ->
        unify_module_bindings
          ~signature:sig_module_bindings
          ~definition:def_module_bindings
      | None -> return def_module_bindings
    in
    let%bind () = add_module ~name:current_name ~module_bindings in
    let open Typed_ast in
    let%map state = State.Result.get in
    let module_name = absolute_name ~state ~name:module_name in
    let module_description = { module_name; functor_args = [] } in
    Module_def (module_description, module_bindings)
  | _ -> failwith "TODO"

and type_toplevel_type (toplevel_type : Ast.toplevel_type) =
  match toplevel_type with
  | Ast.Sig_binding _ -> failwith "TODO"
  | Ast.Sig_module module_description ->
    type_module_description module_description
  | Ast.Sig_type_def _ -> failwith "TODO"

and type_toplevel (toplevel : Ast.toplevel) =
  match toplevel with
  | Ast.Type_def type_def -> type_type_def type_def
  | Ast.Let let_def ->
    let%map let_def = type_let_def let_def in
    Typed_ast.Let let_def
  | Ast.Module_def { module_description; module_def } ->
    type_module ~module_description ~module_def

and substitute_toplevel = function
  | Typed_ast.Type_def _ as x -> return x
  | Typed_ast.Module_def _ as x -> return x
  | Typed_ast.Let let_def ->
    let%map let_def = Typed_ast.map_let_def_monos_m ~f:apply_substs let_def in
    Typed_ast.Let let_def

and type_toplevel_list (l : Ast.t) =
  let%bind.State.Result l = State.Result.all (List.map l ~f:type_toplevel) in
  State.Result.all @@ List.map l ~f:substitute_toplevel
;;

let mono_of_expr e = State.Result.map (type_expr e) ~f:snd

let process_file toplevel_list =
  let%bind toplevels = type_toplevel_list toplevel_list in
  let%map _, module_ = pop_module in
  { module_ with data = Typed_ast.Here toplevels }
;;
