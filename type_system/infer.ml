open! Core
open! Frontend

(* https://pfudke.wordpress.com/2014/11/20/hindley-milner-type-inference-a-practical-example-2/ *)

let gensym =
  let n = ref 0 in
  fun () ->
    let s = !n in
    let letter = Char.of_int_exn (Char.to_int 'a' + (s mod 26)) in
    let s = String.make 1 letter ^ Int.to_string (s / 26) in
    incr n;
    s

type ty =
  | TyVar of Ast.Lowercase.t
  | TyLit of string Ast.Qualified.t
  | TyLambda of ty * ty
[@@deriving sexp, equal, hash, compare]

type env = {
  substs : ty Ast.Lowercase.Map.t;
  vars : (ty * Ast.Lowercase.Set.t) Ast.Lowercase.Map.t;
}
[@@deriving sexp, equal, hash, compare]

let add_constraint env ~var ~ty =
  { env with substs = Map.set env.substs ~key:var ~data:ty }

let rec tyvars_from_type = function
  | TyVar v -> Ast.Lowercase.Set.singleton v
  | TyLambda (a, b) ->
      Ast.Lowercase.Set.union (tyvars_from_type a) (tyvars_from_type b)
  | TyLit _ -> Ast.Lowercase.Set.empty

let rec refine_type env = function
  | TyVar v as x -> (
      match Ast.Lowercase.Map.find env.substs v with
      | Some sub -> refine_type env sub
      | None -> x)
  | TyLambda (a, b) -> TyLambda (refine_type env a, refine_type env b)
  | TyLit l -> TyLit l
