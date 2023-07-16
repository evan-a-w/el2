open! Core
open! Frontend

module Symbol_generator = struct
  type t = { mutable n : int; mutable printed : int } [@@deriving sexp]

  let create () = { n = 0; printed = 0 }

  let gensym t =
    let n = ref 0 in
    fun () ->
      let s = !n in
      let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
      let s = String.make 1 letter ^ Int.to_string (s / 26) in
      incr n;
      s
end

(* TODO: once mutability is added, make mutable type stuff that aren't generalized in let expressions

   should i use mutable fields or have types be mutable/immutable instances??
*)
type mono =
  | Abstract
  | Var of Ast.Lowercase.t
  | Lit of string Ast.Qualified.t
  | Lambda of mono * mono
  | Tuple of mono list
  | Type_function of mono * mono
  | Record of mono * var_map
[@@deriving sexp, equal, hash, compare]

and poly = Mono of mono | Forall of Ast.Lowercase.t * poly
[@@deriving sexp, equal, hash, compare]

and var_map = (mono * Ast.Lowercase.Set.t) Ast.Lowercase.Map.t
and type_map = mono Ast.Lowercase.Map.t

module Module_path = Ast.Qualified.Make (struct
  type arg = Ast.Uppercase.t [@@deriving sexp, compare, equal, hash]
end)

type module_bindings = {
  toplevel_vars : var_map;
  toplevel_types : type_map;
  toplevel_modules : module_bindings Ast.Uppercase.Map.t;
  opened_modules : module_bindings Module_path.Map.t;
}
[@@deriving sexp, equal, hash, compare]

type state = {
  substs : mono Ast.Lowercase.Map.t;
  vars : var_map;
  modules : module_bindings Ast.Uppercase.Map.t;
}
[@@deriving sexp, equal, hash, compare]

let add_constraint state ~var ~ty =
  { state with substs = Map.set state.substs ~key:var ~data:ty }

let rec tyvars_from_type = function
  | Var v -> Ast.Lowercase.Set.singleton v
  | Lambda (a, b) ->
      Ast.Lowercase.Set.union (tyvars_from_type a) (tyvars_from_type b)
  | Lit _ -> Ast.Lowercase.Set.empty
  | _ -> failwith "TODO"

let rec refine_type state = function
  | Var v as x -> (
      match Ast.Lowercase.Map.find state.substs v with
      | Some sub -> refine_type state sub
      | None -> x)
  | Lambda (a, b) -> Lambda (refine_type state a, refine_type state b)
  | Lit _ as a -> a
  | _ -> failwith "TODO"
