open! Core
open! Types

exception Early_exit
exception Unification_error of (mono * mono)

let rec unify (a : mono) (b : mono) =
  let err () = raise (Unification_error (a, b)) in
  let a, b = inner_mono a, inner_mono b in
  if phys_equal a b then raise Early_exit;
  match a, b with
  | `Bottom, o | o, `Bottom -> o
  | `Base (ba, _), `Base (bb, _) when equal_base_type ba bb -> a
  | `Base _, _ | _, `Base _ -> err ()
  | `Pointer a, `Pointer b -> `Pointer (unify a b)
  | `Tuple l1, `Tuple l2 ->
    `Tuple (List.zip_exn l1 l2 |> List.map ~f:(fun (a, b) -> unify a b))
  | `Function (a, b), `Function (c, d) -> `Function (unify a c, unify b d)
  | `Indir (_, c, r), o | o, `Indir (_, c, r) ->
    unify_contraints c o;
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
     | None -> err ()
     | Some a -> unify a o)
  (* Opaque should only unify earlier with user_types exactly matching *)
  | `Opaque _, _ | _, `Opaque _ | _ -> err ()

and unify_contraints _ _ = failwith "TODO"
