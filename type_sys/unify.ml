open! Core
open! Shared
open! Frontend

exception Field_left_only of string
exception Field_right_only of string

exception Unification_error of Ty.mono * Ty.mono
[@deriving sexp]

let occurs_check a mono =
  let open State.Result.Let_syntax in
  let free_vars = free_ty_vars mono in
  match Set.mem free_vars a with
  | true ->
    State.Result.error
      [%message "occurs check failed" (a : Lowercase.t) (mono : mono)]
  | false -> return ()
;;
