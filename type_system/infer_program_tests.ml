open! Core
open! Infer
open! Shared
open! Frontend
open! State.Result.Let_syntax

let program_a =
  {|
type a list = Cons (a, a list) | Nil

type (a, b) result = Ok a | Error b

type a option = Some a | None

type a f = (a -> a)

type alias = int

let rec last = fun x ->
  match x with
  | Cons (x, Nil) -> Some x
  | Cons (_, xs) -> last xs
  | Nil -> None

let x = (1 : a)

let list_of_option = fun (x : a option) ->
  match x with
  | Some x -> Cons (x, Nil)
  | None -> Nil
|}

let run program =
  let action =
    let%bind toplevel_list =
      Parser.try_parse Parser.parse_t program |> State.return
    in
    let%bind module_bindings = process_toplevel_list toplevel_list in
    let%map s = show_module_bindings module_bindings in
    print_endline s
  in
  match State.Result.run action ~state:empty_state with
  | Ok (), _ -> ()
  | Error error, _ -> print_s [%message (error : Sexp.t)]

let%expect_test "program a" =
  run program_a;
  [%expect
    {|
    type alias = int

    type f = a -> a

    type a list = (Enum
     ((type_name (Unqualified list)) (ordering ((a))) (tyvar_map ((a (TyVar a))))
      (level 1))
     ((Cons
       ((Tuple
         ((TyVar a)
          (Recursive_constructor
           ((type_name (Unqualified list)) (ordering ((a)))
            (tyvar_map ((a (TyVar a)))) (level 0)))))))
      (Nil ())))

    type a option = (Enum
     ((type_name (Unqualified option)) (ordering ((a)))
      (tyvar_map ((a (TyVar a)))) (level 1))
     ((Some ((TyVar a))) (None ())))

    type (a, b) result = (Enum
     ((type_name (Unqualified result)) (ordering ((a b)))
      (tyvar_map ((a (TyVar a)) (b (TyVar b)))) (level 1))
     ((Ok ((TyVar a))) (Error ((TyVar b)))))

    let last : a list -> a option

    let list_of_option : a option -> a list

    let x : int |}]
