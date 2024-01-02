open! Core

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
  { repr_name : string
  ; ty_vars : string list
  ; info : all_user option ref
  }

and inst_user_type_info =
  | Insted of user_type
  | To_inst of user_type

and inst_user_type =
  { monos : mono list
  ; mutable user_type : inst_user_type_info
  ; mutable inst_user_mono : mono option
  (* if user_type is an alias, this is the mono that comes from mapping ty_vars to the replacement mono *)
  }

and enum_type = [ `Enum of (string * mono) list ]
and struct_type = [ `Struct of (string * mono) list ]

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
  | ( `User { monos = inst1; user_type = r1; _ }
    , `User { monos = inst2; user_type = r2; _ } ) ->
    (match [%compare: mono list] inst1 inst2 with
     | 0 -> compare_inst_user_type_info r1 r2
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

and compare_inst_user_type_info u u' =
  let get = function
    | Insted x -> x
    | To_inst x -> x
  in
  compare_user_type (get u) (get u')

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
  let sexp_of_inst_user_type_info = sexp_of_inst_user_type_info_seen ~seen in
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
  | `User { monos; user_type; _ } ->
    Sexp.List
      [ [%sexp "User"]
      ; [%sexp_of: mono list] monos
      ; [%sexp (user_type : inst_user_type_info)]
      ]
  | `Function (a, b) ->
    Sexp.List [ [%sexp "Function"]; sexp_of_mono a; sexp_of_mono b ]
  | `Opaque m -> Sexp.List [ [%sexp "Opaque"]; sexp_of_mono m ]
  | `Pointer m -> Sexp.List [ [%sexp "Pointer"]; sexp_of_mono m ]

and sexp_of_inst_user_type_info_seen ~seen = function
  | Insted x -> Sexp.List [ Sexp.Atom "Insted"; sexp_of_user_type_seen x ~seen ]
  | To_inst x ->
    Sexp.List [ Sexp.Atom "To_inst"; sexp_of_user_type_seen x ~seen ]

and sexp_of_user_type_seen ~seen ({ repr_name; ty_vars; info } as user_type) =
  let sexp_of_all_user = sexp_of_all_user_seen ~seen in
  match Hash_set.mem seen user_type.repr_name with
  | true -> Sexp.Atom user_type.repr_name
  | false ->
    Hash_set.add seen user_type.repr_name;
    Sexp.List
      [ sexp_of_string repr_name
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
  | List [ Atom "User"; inst; user ] ->
    let monos = [%of_sexp: mono list] inst in
    `User
      { monos
      ; user_type = inst_user_type_info_of_sexp_seen ~seen user
      ; inst_user_mono = None
      }
  | _ -> failwith [%string "Invalid mono sexp %{sexp#Sexp}"]

and inst_user_type_info_of_sexp_seen ~seen sexp =
  match sexp with
  | Sexp.List [ Atom "Insted"; rest ] ->
    Insted (user_type_ref_of_sexp_seen ~seen rest)
  | Sexp.List [ Atom "To_inst"; rest ] ->
    To_inst (user_type_ref_of_sexp_seen ~seen rest)
  | _ -> failwith [%string "Invalid user_type sexp %{sexp#Sexp}"]

and user_type_ref_of_sexp_seen ~seen sexp =
  match sexp with
  | Sexp.Atom repr_name ->
    (match Hashtbl.find seen repr_name with
     | None -> failwith [%string "Invalid user_type sexp %{sexp#Sexp}"]
     | Some x -> x)
  | List [ repr_name; ty_vars; info ] ->
    let initial =
      { repr_name = string_of_sexp repr_name
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
  user_type_ref_of_sexp_seen ~seen:(String.Table.create ()) user_type
;;

let%expect_test "recursive_types_sexp" =
  let rec user_type_a =
    { repr_name = "A"
    ; ty_vars = []
    ; info =
        ref
          (Some
             (`Alias
               (`User
                 { monos = []
                 ; user_type = Insted user_type_b
                 ; inst_user_mono = None
                 })))
    }
  and user_type_b =
    { repr_name = "B"
    ; ty_vars = []
    ; info =
        ref
          (Some
             (`Alias
               (`User
                 { monos = []
                 ; user_type = Insted user_type_a
                 ; inst_user_mono = None
                 })))
    }
  in
  let sexp_a = [%sexp (user_type_a : user_type)] in
  print_s sexp_a;
  let sexp_b = [%sexp (user_type_b : user_type)] in
  print_s sexp_b;
  let user_type_a' = user_type_of_sexp sexp_a in
  print_s [%sexp (user_type_a' : user_type)];
  let user_type_b' = user_type_of_sexp sexp_b in
  print_s [%sexp (user_type_b' : user_type)];
  [%expect
    {|
    (A () ((Alias (User () (Insted (B () ((Alias (User () (Insted A))))))))))
    (B () ((Alias (User () (Insted (A () ((Alias (User () (Insted B))))))))))
    (A () ((Alias (User () (Insted (B () ((Alias (User () (Insted A))))))))))
    (B () ((Alias (User () (Insted (A () ((Alias (User () (Insted B)))))))))) |}];
  assert (0 = compare_user_type user_type_a user_type_a');
  assert (0 <> compare_user_type user_type_a user_type_b)
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
    | `User { monos; user_type; _ } ->
      `User
        { monos = List.map monos ~f:go
        ; user_type =
            go_inst_user_type_info_map_rec
              ~user_type_mem
              ~f
              ~on_var
              ~on_indir
              user_type
        ; inst_user_mono = None
        }
  in
  f mono

and go_inst_user_type_info_map_rec ~user_type_mem ~f ~on_var ~on_indir user_type
  =
  match user_type with
  | Insted x ->
    Insted (go_user_type_map_rec ~user_type_mem ~f ~on_var ~on_indir x)
  | To_inst x ->
    To_inst (go_user_type_map_rec ~user_type_mem ~f ~on_var ~on_indir x)

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
    let { repr_name; _ } =
      match inst.user_type with
      | Insted x -> x
      | To_inst x -> x
    in
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

and show_user_type_inst
  { monos; user_type = Insted user_type | To_inst user_type; _ }
  =
  let monos = show_mono (`Tuple monos) in
  let user_type = show_user_type user_type in
  [%string "{  %{monos}; %{user_type}; }"]
;;

(* TODO: convinced bug is once again here, cache inst of user type
   based on mono args when inst_user_type is called *)
let do_inst_user_type ~monos user_type =
  let rep_map =
    List.zip_exn user_type.ty_vars monos |> String.Map.of_alist_exn
  in
  user_type_map_rec
    ~on_var:(Fn.const None)
    ~on_indir:(Fn.const None)
    ~f:(function
      | `Var (s, _) as mono -> Map.find rep_map s |> Option.value ~default:mono
      | o -> o)
    user_type
;;

let inst_user_type user_type ~(monos : mono list) : inst_user_type =
  let user_type =
    match !(user_type.info) with
    | None -> To_inst user_type
    | Some _ ->
      let res = do_inst_user_type ~monos user_type in
      Insted res
  in
  { monos; user_type; inst_user_mono = None }
;;

let get_user_type inst_user_type =
  match inst_user_type.user_type with
  | Insted user_type -> user_type
  | To_inst user_type ->
    let res = do_inst_user_type user_type ~monos:inst_user_type.monos in
    inst_user_type.user_type <- Insted res;
    res
;;

let user_type = get_user_type
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
  inner_mono mono
  |> mono_map_rec_keep_refs ~f:(fun mono ->
    match mono with
    | `Var (s, _) -> Map.find inst_map s |> Option.value ~default:mono
    | _ -> mono)
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

let user_type_monify ({ monos; inst_user_mono; _ } as inst) =
  let { repr_name = _; ty_vars; info } = user_type inst in
  match inst_user_mono with
  | Some _ -> inst_user_mono
  | None ->
    let rep_map = List.zip_exn ty_vars monos |> String.Table.of_alist_exn in
    (match !info with
     | Some (`Alias m) ->
       let mono =
         mono_map_rec_keep_refs m ~f:(function
           | `Var (s, _) when Hashtbl.mem rep_map s ->
             Hashtbl.find_exn rep_map s
           | other -> other)
       in
       inst.inst_user_mono <- Some mono;
       Some mono
     | _ -> None)
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
    let { repr_name; _ } = user_type inst in
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
