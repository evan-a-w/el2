open! Core

(* TODO: add array types (stack allocated) - currently unsound because
   array literals are shared basically *)

(*SUA *)
open! Ast

type enum
type struct_

module Counter = struct
  type t = (int ref[@ignore]) [@@deriving sexp, compare, hash, equal]

  let create () = ref 0

  let next_int t =
    let res = !t in
    incr t;
    res
  ;;

  let next_num t =
    let res = !t in
    incr t;
    Int.to_string res
  ;;

  let next_alphabetical t =
    let i = next_int t in
    let char, rest = i % 26, i / 26 in
    [%string {|%{"abcdefghijklmnopqrstuvwxyz".[char]#Char}%{rest#Int}|}]
  ;;
end

(* global *)
let indir_counter = Counter.create ()
let get a = Option.value_exn !a
let set a a' = a := Some a'

(* Can be cycles in user_type, compare just uses the name and tyvars *)
(* indir and var stuff form dags *)
type mono =
  [ `Unit
  | `C_int
  | `I64
  | `F64
  | `Bool
  | `Char
  | `Pointer of mono
  | `Opaque of mono
  | `Tuple of mono list
  | `Function of mono * mono
  | `User of inst_user_type
  | `Indir of int * mono option ref
  | `Var of string * mono option ref
  ]

and mono_var_replacements = (string * mono) list

and user_type =
  { name : string
  ; repr_name : string
  ; ty_vars : string list
  ; info : all_user option ref
  }

and inst_user_type =
  { monos : mono list
  ; orig_user_type : user_type
  ; insted_user_type : user_type option ref
  }

and all_user =
  [ `Enum of (string * mono option) list
  | `Struct of (string * mono) list
  | `Alias of mono
  ]
[@@deriving sexp]

let inner_mono_non_rec mono =
  match mono with
  | `Var (_, { contents = Some mono' }) | `Indir (_, { contents = Some mono' })
    -> mono'
  | other -> other
;;

let rec collapse_mono (mono : mono) =
  match mono with
  | `Var (_, { contents = None }) | `Indir (_, { contents = None }) -> mono
  | `Indir (_, ({ contents = Some mono' } as r))
  | `Var (_, ({ contents = Some mono' } as r)) ->
    let res = collapse_mono mono' |> inner_mono_non_rec in
    set r res;
    res
  | _ -> mono
;;

let rec inner_mono mono =
  let mono = collapse_mono mono in
  match mono with
  | `Var (_, { contents = Some mono' }) | `Indir (_, { contents = Some mono' })
    -> inner_mono mono'
  | other -> other
;;

let is_free (mono : mono) =
  let mono = collapse_mono mono in
  match mono with
  | `Var (_, { contents = None }) | `Indir (_, { contents = None }) -> true
  | _ -> false
;;

let rec compare_mono (m : mono) (m' : mono) =
  let m = collapse_mono m in
  let m' = collapse_mono m' in
  match m, m' with
  | _, _ when phys_equal m m' -> 0
  | `Unit, `Unit
  | `I64, `I64
  | `F64, `F64
  | `Bool, `Bool
  | `Char, `Char
  | `C_int, `C_int -> 0
  | `Pointer m, `Pointer m' | `Opaque m, `Opaque m' -> compare_mono m m'
  | `Function (a, b), `Function (a', b') ->
    [%compare: mono * mono] (a, b) (a', b')
  | `Tuple l, `Tuple l' -> [%compare: mono list] l l'
  | ( `User { monos = inst1; orig_user_type = r1; _ }
    , `User { monos = inst2; orig_user_type = r2; _ } ) ->
    (match [%compare: mono list] inst1 inst2 with
     | 0 -> compare_user_type r1 r2
     | other -> other)
  | (`Indir (_, ra), `Indir (_, rb) | `Var (_, ra), `Var (_, rb))
    when phys_equal ra rb -> 0
  | `Indir (a, _), `Indir (b, _) -> a - b
  | `Var (s, _), `Var (s', _) -> String.compare s s'
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

type poly =
  [ `Mono of mono
  | `For_all of string * poly
  ]
[@@deriving sexp, compare]

let make_indir () =
  let id = Counter.next_int indir_counter in
  `Indir (id, ref None)
;;

let make_var_mono name : mono = `Var (name, ref None)

include struct
  module T = struct
    type t = mono [@@deriving sexp, compare]
  end

  module Mono_set = Set.Make (T)
  module Mono_map = Map.Make (T)
end

module User_type_map = Map.Make (struct
    type t = user_type [@@deriving sexp, compare]
  end)

let duplicate_user_type (name, _) = make_var_mono name

let rec go_mono_map_rec ~user_type_mem (mono : mono) ~f ~on_var ~on_indir =
  let go = go_mono_map_rec ~user_type_mem ~f ~on_var ~on_indir in
  let mono = collapse_mono mono in
  let mono =
    match mono with
    | `Unit | `C_int | `I64 | `F64 | `Bool | `Char -> mono
    | `Pointer m -> `Pointer (go m)
    | `Opaque m -> `Opaque (go m)
    | `Function (a, b) -> `Function (go a, go b)
    | `Tuple l -> `Tuple (List.map l ~f:go)
    | `Indir r -> Option.value (on_indir r) ~default:mono
    | `Var r -> Option.value (on_var r) ~default:mono
    | `User { monos; orig_user_type; insted_user_type } ->
      let user = go_user_type_map_rec ~user_type_mem ~f ~on_var ~on_indir in
      `User
        { monos = List.map monos ~f:go
        ; orig_user_type
        ; insted_user_type = ref (Option.map ~f:user !insted_user_type)
        }
  in
  f mono

and go_user_type_map_rec ~user_type_mem ~f ~on_var ~on_indir user_type =
  match Map.find !user_type_mem user_type.repr_name with
  | Some res -> res
  | None ->
    let res = { user_type with info = ref None } in
    user_type_mem := Map.set !user_type_mem ~key:user_type.repr_name ~data:res;
    res.info
    := Option.map
         ~f:(go_all_user_map_rec ~user_type_mem ~f ~on_var ~on_indir)
         !(user_type.info);
    res

and go_all_user_map_rec ~user_type_mem ~f ~on_var ~on_indir =
  let go_mono = go_mono_map_rec ~user_type_mem ~f ~on_var ~on_indir in
  function
  | `Enum l -> `Enum (List.map l ~f:(fun (s, m) -> s, Option.map ~f:go_mono m))
  | `Struct l -> `Struct (List.map l ~f:(fun (s, m) -> s, go_mono m))
  | `Alias m -> `Alias (go_mono m)
;;

let mono_map_rec mono ~f =
  let user_type_mem = ref String.Map.empty in
  go_mono_map_rec ~user_type_mem mono ~f
;;

let mono_map_rec_keep_refs mono ~f =
  let user_type_mem = ref String.Map.empty in
  go_mono_map_rec
    ~user_type_mem
    mono
    ~f
    ~on_var:(Fn.const None)
    ~on_indir:(Fn.const None)
;;

let user_type_map_rec user_type ~f =
  let user_type_mem = ref String.Map.empty in
  go_user_type_map_rec ~user_type_mem user_type ~f
;;

let rec show_mono (mono : mono) =
  let mono = collapse_mono mono in
  match mono with
  | `Bool -> "bool"
  | `C_int -> "c_int"
  | `I64 -> "i64"
  | `F64 -> "f64"
  | `Unit -> "unit"
  | `Char -> "char"
  | `User inst ->
    let { repr_name; _ } = inst.orig_user_type in
    let monos =
      match inst.monos with
      | [] -> ""
      | l -> "(" ^ (List.map l ~f:show_mono |> String.concat ~sep:", ") ^ ")"
    in
    repr_name ^ monos
  | `Function (a, b) -> show_mono a ^ " -> " ^ show_mono b
  | `Opaque x -> [%string "opaque(%{show_mono x})"]
  | `Pointer x -> "&(" ^ show_mono x ^ ")"
  | `Tuple l -> "(" ^ (List.map l ~f:show_mono |> String.concat ~sep:", ") ^ ")"
  | `Indir (id, _) -> [%string "weak_%{id#Int}"]
  | `Var (s, _) -> s

and show_mono_deep mono =
  match mono with
  | `User x -> show_user_type_inst x
  | _ -> show_mono mono

and show_user_type user_type =
  let show_user_type_inner buf user_type =
    match !(user_type.info) with
    | Some (`Alias m) ->
      Buffer.add_string buf "alias ";
      Buffer.add_string buf (show_mono m)
    | Some (`Enum l) ->
      Buffer.add_string buf "enum { ";
      List.iter l ~f:(fun (s, m) ->
        Buffer.add_string buf s;
        Buffer.add_string buf " = ";
        Buffer.add_string buf (Option.value_map m ~default:"" ~f:show_mono);
        Buffer.add_string buf "; ");
      Buffer.add_string buf "}"
    | Some (`Struct l) ->
      Buffer.add_string buf "struct { ";
      List.iter l ~f:(fun (s, m) ->
        Buffer.add_string buf s;
        Buffer.add_string buf " : ";
        Buffer.add_string buf (show_mono m);
        Buffer.add_string buf "; ");
      Buffer.add_string buf "}"
    | None -> Buffer.add_string buf "unknown"
  in
  let buf = Buffer.create 16 in
  Buffer.add_string buf user_type.repr_name;
  (match user_type.ty_vars with
   | [] -> ()
   | l ->
     Buffer.add_char buf '(';
     Buffer.add_string buf (String.concat ~sep:"," l);
     Buffer.add_char buf ')');
  Buffer.add_string buf " = ";
  show_user_type_inner buf user_type;
  Buffer.contents buf

and show_user_type_inst { monos; orig_user_type; _ } =
  let monos = show_mono (`Tuple monos) in
  let user_type = show_user_type orig_user_type in
  [%string "{  %{monos}; %{user_type}; }"]
;;

module Ut = Map.Make (struct
    type t = mono list * string [@@deriving sexp, compare]
  end)

type cache =
  { mutable inst_user_types : mono Ut.t
  ; mutable user_types : user_type Ut.t
  }

let cache_create () = { inst_user_types = Ut.empty; user_types = Ut.empty }

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
      List.fold2_exn
        user_type.ty_vars
        monos
        ~init:rep_map
        ~f:(fun acc key data -> Map.set acc ~key ~data)
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
  | `Unit | `C_int | `I64 | `F64 | `Bool | `Char | `Indir _ | `Var _ -> mono
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

let show_mono = show_mono_deep

let show_poly poly =
  let rec show_poly_inner buf = function
    | `Mono mono ->
      Buffer.add_string buf ". ";
      Buffer.add_string buf (show_mono mono)
    | `For_all (a, b) ->
      Buffer.add_string buf a;
      Buffer.add_char buf ' ';
      show_poly_inner buf b
  in
  match poly with
  | `Mono mono -> show_mono mono
  | _ ->
    let buf = Buffer.create 16 in
    show_poly_inner buf poly;
    Buffer.contents buf
;;

let inst_mono ~inst_map mono =
  inner_mono mono |> do_inst_mono ~cache:(cache_create ()) ~rep_map:inst_map
;;

let inst poly =
  let rec go vars = function
    | `Mono mono -> inst_mono mono ~inst_map:vars, vars
    | `For_all (a, r) -> go (Map.set vars ~key:a ~data:(make_indir ())) r
  in
  go String.Map.empty poly
;;

let inst_user_type_gen user_type =
  let monos = List.map user_type.ty_vars ~f:(fun _ -> make_indir ()) in
  inst_user_type ~monos user_type
;;

let user_type_monify inst =
  let user_type = get_insted_user_type inst in
  match user_type with
  | Some { info = { contents = Some (`Alias m) }; _ } -> Some m
  | _ -> None
;;

let rec string_of_mono (mono : mono) =
  let mono = collapse_mono mono in
  match mono with
  | `Bool -> "bool"
  | `C_int -> "cint"
  | `I64 -> "i64"
  | `F64 -> "f64"
  | `Unit -> "unit"
  | `Char -> "char"
  | `User inst ->
    let { repr_name; _ } = inst.orig_user_type in
    (match inst.monos with
     | [] -> repr_name
     | l ->
       let s = List.map l ~f:string_of_mono |> String.concat ~sep:"_" in
       repr_name ^ "_of_" ^ s)
  | `Function (a, b) -> string_of_mono a ^ "_to_" ^ string_of_mono b
  | `Opaque _ -> "opaque"
  | `Pointer x -> "pointer_of_" ^ string_of_mono x
  | `Tuple l -> List.map l ~f:string_of_mono |> String.concat ~sep:"_and_"
  | `Indir (id, _) -> [%string "weak_%{id#Int}"]
  | `Var (s, _) -> s
;;

let rec recover_inst_map poly mono inst_map =
  let poly = inner_mono poly in
  let mono = inner_mono mono in
  match poly, mono with
  | `Var (s, _), _ -> Map.set inst_map ~key:s ~data:mono
  | `Indir _, _
  | `Bool, `Bool
  | `C_int, `C_int
  | `I64, `I64
  | `F64, `F64
  | `Unit, `Unit
  | `Char, `Char -> inst_map
  | `Pointer p, `Pointer p' -> recover_inst_map p p' inst_map
  | `Opaque p, `Opaque p' -> recover_inst_map p p' inst_map
  | `Function (a, b), `Function (a', b') ->
    recover_inst_map a a' inst_map |> recover_inst_map b b'
  | `User { monos = l; _ }, `User { monos = l'; _ } | `Tuple l, `Tuple l' ->
    List.fold2_exn l l' ~init:inst_map ~f:(fun acc a b ->
      recover_inst_map a b acc)
  | _ -> inst_map
;;
