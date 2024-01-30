open! Core

type base_type =
  [ `Unit
  | `C_int
  | `I64
  | `F64
  | `Bool
  | `Char
  ]
[@@deriving sexp, compare, equal]

type mono =
  [ `Base of base_type_with_impl
  | `Bottom
  | `Pointer of mono
  | `Opaque of mono
  | `Tuple of mono list
  | `Function of mono * mono
  | `User of inst_user_type
  | `Indir of int * type_members * mono option ref
  ]

and base_type_with_impl = base_type * type_members

and type_members =
  { methods : mono String.Table.t
  ; fields : mono String.Table.t
  }

and user_type =
  { name : string
  ; repr_name : string
  ; ty_vars : string list
  ; info : type_def option ref
  ; members : type_members
  }

and inst_user_type =
  { monos : mono list
  ; orig_user_type : user_type
  ; insted_user_type : user_type option ref
  }

and type_def =
  [ `Enum of (string * mono option) list
  | `Struct of (string * mono) list
  | `Alias of mono
  ]
[@@deriving sexp]

let inner_mono_non_rec (mono : mono) =
  match mono with
  | `Indir (_, _, { contents = Some mono' }) -> mono'
  | other -> other
;;

let rec collapse_mono (mono : mono) =
  match mono with
  | `Indir (_, _, { contents = None }) -> mono
  | `Indir (_, _, ({ contents = Some mono' } as r)) ->
    let res = collapse_mono mono' |> inner_mono_non_rec in
    r := Some res;
    res
  | _ -> mono
;;

let rec inner_mono mono =
  let mono = collapse_mono mono in
  match mono with
  | `Indir (_, _, { contents = Some mono' }) -> inner_mono mono'
  | other -> other
;;

let rec compare_mono (m : mono) (m' : mono) =
  let m = collapse_mono m in
  let m' = collapse_mono m' in
  match m, m' with
  | _, _ when phys_equal m m' -> 0
  | `Bottom, `Bottom
  | `Base (`Unit, _), `Base (`Unit, _)
  | `Base (`I64, _), `Base (`I64, _)
  | `Base (`F64, _), `Base (`F64, _)
  | `Base (`Bool, _), `Base (`Bool, _)
  | `Base (`Char, _), `Base (`Char, _)
  | `Base (`C_int, _), `Base (`C_int, _) -> 0
  | `Pointer m, `Pointer m' | `Opaque m, `Opaque m' -> compare_mono m m'
  | `Function (a, b), `Function (a', b') ->
    [%compare: mono * mono] (a, b) (a', b')
  | `Tuple l, `Tuple l' -> [%compare: mono list] l l'
  | ( `User { monos = inst1; orig_user_type = r1; _ }
    , `User { monos = inst2; orig_user_type = r2; _ } ) ->
    (match [%compare: mono list] inst1 inst2 with
     | 0 -> compare_user_type r1 r2
     | other -> other)
  | `Indir (_, _, ra), `Indir (_, _, rb) when phys_equal ra rb -> 0
  | `Indir (a, _, _), `Indir (b, _, _) -> a - b
  | `Bottom, _ -> -1
  | _, `Bottom -> 1
  | `Unit, _ -> -1
  | _, `Unit -> 1
  | `C_int, _ -> -1
  | _, `C_int -> 1
  | `I64, _ -> -1
  | _, `I64 -> 1
  | `F64, _ -> -1
  | _, `F64 -> 1
  | `Bool, _ -> -1
  | _, `Bool -> 1
  | `Char, _ -> -1
  | _, `Char -> 1
  | `Pointer _, _ -> -1
  | _, `Pointer _ -> 1
  | `Opaque _, _ -> -1
  | _, `Opaque _ -> 1
  | `Tuple _, _ -> -1
  | _, `Tuple _ -> 1
  | `Function (_, _), _ -> -1
  | _, `Function (_, _) -> 1
  | `User _, _ -> -1
  | _, `User _ -> 1
  | `Indir _, _ -> -1
  | _, `Indir _ -> 1

and compare_user_type u u' =
  [%compare: string list * string]
    (u.ty_vars, u.repr_name)
    (u'.ty_vars, u'.repr_name)

and compare_all_user a a' =
  match a, a' with
  | `Struct s, `Struct s' -> [%compare: (string * mono) list] s s'
  | `Alias m, `Alias m' -> compare_mono m m'
  | `Enum e, `Enum e' -> [%compare: (string * mono option) list] e e'
  | `Struct _, _ -> -1
  | _, `Struct _ -> 1
  | `Enum _, _ -> -1
  | _, `Enum _ -> 1
;;

let rec sexp_of_mono_seen ~seen m =
  let sexp_of_mono = sexp_of_mono_seen ~seen in
  let m = collapse_mono m in
  match m with
  | `Bottom -> [%sexp "Bottom"]
  | `Unit -> [%sexp "Unit"]
  | `Bool -> [%sexp "Bool"]
  | `Char -> [%sexp "Char"]
  | `C_int -> [%sexp "C_int"]
  | `I64 -> [%sexp "I64"]
  | `F64 -> [%sexp "F64"]
  | `Tuple l -> [%sexp_of: mono list] l
  | `Indir (id, m) ->
    Sexp.List [ [%sexp "Indir"]; sexp_of_int id; [%sexp_of: mono option ref] m ]
  | `Var (name, m) ->
    Sexp.List
      [ [%sexp "Var"]; [%sexp (name : string)]; [%sexp_of: mono option ref] m ]
  | `User { monos; orig_user_type; insted_user_type } ->
    Sexp.List
      [ [%sexp "User"]
      ; [%sexp_of: mono list] monos
      ; [%sexp (orig_user_type : user_type)]
      ; [%sexp (insted_user_type : user_type option ref)]
      ]
  | `Function (a, b) ->
    Sexp.List [ [%sexp "Function"]; sexp_of_mono a; sexp_of_mono b ]
  | `Opaque m -> Sexp.List [ [%sexp "Opaque"]; sexp_of_mono m ]
  | `Pointer m -> Sexp.List [ [%sexp "Pointer"]; sexp_of_mono m ]

and sexp_of_user_type_seen
  ~seen
  ({ repr_name; ty_vars; info; name } as user_type)
  =
  let sexp_of_all_user = sexp_of_all_user_seen ~seen in
  match Hash_set.mem seen user_type.repr_name with
  | true -> [%sexp_of: string * string] (repr_name, name)
  | false ->
    Hash_set.add seen user_type.repr_name;
    Sexp.List
      [ [%sexp_of: string * string] (repr_name, name)
      ; [%sexp (ty_vars : string list)]
      ; [%sexp (info : all_user option ref)]
      ]

and sexp_of_all_user_seen ~seen =
  let sexp_of_mono = sexp_of_mono_seen ~seen in
  function
  | `Struct l ->
    Sexp.List [ sexp_of_string "Struct"; [%sexp (l : (string * mono) list)] ]
  | `Alias m -> Sexp.List [ sexp_of_string "Alias"; sexp_of_mono m ]
  | `Enum l ->
    Sexp.List
      [ sexp_of_string "Enum"; [%sexp (l : (string * mono option) list)] ]
;;

let sexp_of_mono a = sexp_of_mono_seen ~seen:(String.Hash_set.create ()) a

let sexp_of_user_type a =
  sexp_of_user_type_seen ~seen:(String.Hash_set.create ()) a
;;

let sexp_of_all_user a =
  sexp_of_all_user_seen ~seen:(String.Hash_set.create ()) a
;;

let rec mono_of_sexp_seen ~seen sexp : mono =
  let user_type_of_sexp = user_type_of_sexp_seen ~seen in
  let mono_of_sexp = mono_of_sexp_seen ~seen in
  match sexp with
  | Sexp.Atom "Unit" -> `Unit
  | Atom "Bool" -> `Bool
  | Atom "Char" -> `Char
  | Atom "I64" -> `I64
  | Atom "F64" -> `F64
  | List [ Atom "Indir"; id; Atom "None" ] -> `Indir (int_of_sexp id, ref None)
  | List [ Atom "Indir"; id; List [ Atom "Some"; mono ] ] ->
    `Indir (int_of_sexp id, ref (Some (mono_of_sexp mono)))
  | List [ Atom "Var"; name; Atom "None" ] ->
    `Var (string_of_sexp name, ref None)
  | List [ Atom "Var"; name; List [ Atom "Some"; mono ] ] ->
    `Var (string_of_sexp name, ref (Some (mono_of_sexp mono)))
  | List [ Atom "User"; inst; orig_user; insted ] ->
    let monos = [%of_sexp: mono list] inst in
    `User
      { monos
      ; orig_user_type = user_type_of_sexp_seen ~seen orig_user
      ; insted_user_type = ref ([%of_sexp: user_type option] insted)
      }
  | _ -> failwith [%string "Invalid mono sexp %{sexp#Sexp}"]

and user_type_of_sexp_seen ~seen sexp =
  match sexp with
  | Sexp.Atom repr_name ->
    (match Hashtbl.find seen repr_name with
     | None -> failwith [%string "Invalid user_type sexp %{sexp#Sexp}"]
     | Some x -> x)
  | List [ repr_name; ty_vars; info ] ->
    let repr_name, name = [%of_sexp: string * string] repr_name in
    let initial =
      { repr_name
      ; name
      ; ty_vars = [%of_sexp: string list] ty_vars
      ; info = ref None
      }
    in
    Hashtbl.add_exn seen ~key:initial.repr_name ~data:initial;
    let all_user_of_sexp = all_user_of_sexp_seen ~seen in
    let info = [%of_sexp: all_user option] info in
    initial.info := info;
    initial
  | _ -> failwith [%string "Invalid user_type sexp %{sexp#Sexp}"]

and all_user_of_sexp_seen ~seen sexp =
  let mono_of_sexp = mono_of_sexp_seen ~seen in
  match sexp with
  | Sexp.List [ Atom "Struct"; l ] ->
    `Struct ([%of_sexp: (string * mono) list] l)
  | Sexp.List [ Atom "Enum"; l ] ->
    `Enum ([%of_sexp: (string * mono option) list] l)
  | Sexp.List [ Atom "Alias"; m ] -> `Alias (mono_of_sexp m)
  | _ -> failwith [%string "Invalid all_user sexp %{sexp#Sexp}"]
;;

let mono_of_sexp a = mono_of_sexp_seen ~seen:(String.Table.create ()) a
let all_user_of_sexp a = all_user_of_sexp_seen ~seen:(String.Table.create ()) a

let user_type_of_sexp user_type =
  user_type_of_sexp_seen ~seen:(String.Table.create ()) user_type
;;

module Ut = Map.Make (struct
    type t = mono list * string [@@deriving sexp, compare]
  end)

type cache =
  { mutable inst_user_types : mono Ut.t
  ; mutable user_types : user_type Ut.t
  }

let rec do_inst_user_type ~(cache : cache) ~rep_map inst_user_type =
  let monos = List.map ~f:(do_inst_mono ~cache ~rep_map) inst_user_type.monos in
  match
    Map.find
      cache.inst_user_types
      (monos, inst_user_type.orig_user_type.repr_name)
  with
  | Some x -> x
  | None ->
    `User
      (do_inst_user_type_inner
         ~cache
         ~rep_map
         ~monos
         inst_user_type.orig_user_type)

and do_inst_user_type_inner ~cache ~rep_map ~monos orig_user_type =
  let inst = { monos; orig_user_type; insted_user_type = ref None } in
  cache.inst_user_types
    <- Map.set
         cache.inst_user_types
         ~key:(monos, orig_user_type.repr_name)
         ~data:(`User inst);
  let insted_user_type =
    do_inst_actual_user_type ~cache ~monos orig_user_type ~rep_map
  in
  inst.insted_user_type := insted_user_type;
  inst

and do_inst_actual_user_type ~cache ~rep_map ~monos user_type : user_type option
  =
  match
    Map.find cache.user_types (monos, user_type.repr_name), !(user_type.info)
  with
  | Some x, _ -> Some x
  | None, None -> None
  | None, Some info ->
    let res = { user_type with info = ref None } in
    cache.user_types
      <- Map.set cache.user_types ~key:(monos, user_type.repr_name) ~data:res;
    let rep_map =
      match
        List.fold2 user_type.ty_vars monos ~init:rep_map ~f:(fun acc key data ->
          Map.set acc ~key ~data)
      with
      | Ok x -> x
      | Unequal_lengths ->
        failwith
          [%string
            "Unequal list lengths in user_type: len %{List.length monos#Int}, \
             expected: %{List.length user_type.ty_vars#Int}"]
    in
    res.info := Some (do_inst_all_user ~cache ~rep_map info);
    Some res

and do_inst_all_user ~cache ~rep_map (all_user : all_user) =
  let go_mono = do_inst_mono ~cache ~rep_map in
  match all_user with
  | `Enum l -> `Enum (List.map l ~f:(fun (s, m) -> s, Option.map ~f:go_mono m))
  | `Struct l -> `Struct (List.map l ~f:(fun (s, m) -> s, go_mono m))
  | `Alias m -> `Alias (go_mono m)

and do_inst_mono ~cache ~rep_map mono =
  let go = do_inst_mono ~cache ~rep_map in
  let mono = inner_mono mono in
  match mono with
  | `Var (s, _) when Map.mem rep_map s -> Map.find_exn rep_map s
  | `Unit | `C_int | `I64 | `F64 | `Bool | `Char | `Bottom | `Indir _ | `Var _
    -> mono
  | `Pointer m -> `Pointer (go m)
  | `Opaque m -> `Opaque (go m)
  | `Function (a, b) -> `Function (go a, go b)
  | `Tuple l -> `Tuple (List.map l ~f:go)
  | `User inst_user_type -> do_inst_user_type ~cache ~rep_map inst_user_type

and do_get_insted_user_type ~cache ~rep_map inst_user_type =
  match !(inst_user_type.insted_user_type) with
  | Some _ as x -> x
  | None ->
    let res =
      do_inst_actual_user_type
        inst_user_type.orig_user_type
        ~monos:inst_user_type.monos
        ~cache
        ~rep_map
    in
    inst_user_type.insted_user_type := res;
    res
;;

let get_insted_user_type inst =
  do_get_insted_user_type
    ~cache:{ user_types = Ut.empty; inst_user_types = Ut.empty }
    ~rep_map:String.Map.empty
    inst
;;

let inst_user_type user_type ~(monos : mono list) : inst_user_type =
  do_inst_user_type_inner
    ~cache:(cache_create ())
    ~rep_map:String.Map.empty
    ~monos
    user_type
;;
