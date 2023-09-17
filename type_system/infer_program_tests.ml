open! Core
open! Infer
open! Inference_state
open! Shared
open! Frontend
open! State.Result.Let_syntax
open! Monos

let run program =
  let action =
    let%bind toplevel_list =
      Parser.try_parse Parser.parse_t program |> State.return
    in
    let%bind _ = type_toplevel_list toplevel_list in
    let%bind _, module_bindings = pop_module in
    let%map s = show_module_bindings module_bindings in
    print_endline s
    (* print_s [%sexp (toplevels : Typed_ast.toplevel list)] *)
  in
  match
    State.Result.run action ~state:(empty_state (Qualified.Unqualified "Test"))
  with
  | Ok (), _ -> ()
  | Error error, _ -> print_s [%message (error : Sexp.t)]
;;

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
;;

let%expect_test "program a" =
  run program_a;
  [%expect
    {|
    type alias = int

    type a f = a -> a

    type a list =
    	| Cons (a, a list)
    	| Nil

    type a option =
    	| Some a
    	| None

    type (a, b) result =
    	| Ok a
    	| Error b

    let last : a list -> a option

    let list_of_option : a option -> a list

    let x : int |}]
;;

let program_b =
  {|
type a list = Cons (a, a list) | Nil

module X = struct
    type t = Pee
end

type t = X.t |}
;;

let%expect_test "program b" =
  run program_b;
  [%expect
    {|
    type a list =
    	| Cons (a, a list)
    	| Nil

    type t = X.t

    module X = struct
        type t =
        	| Pee
    end |}]
;;

let program_c =
  {|
type a has_closure = { f : int -{a}> int }

let g = fun { f } -> f |}
;;

let%expect_test "program c" =
  run program_c;
  [%expect
    {|
    type a has_closure = ((f
      ((Closure
        (Named
         ((type_name int) (absolute_type_name (Unqualified int)) (ordering ())
          (tyvar_map ()) (type_id 173207638) (mem_rep (Closed Bits32))
          (user_type (Abstract (Closed Bits32)))))
        (Named
         ((type_name int) (absolute_type_name (Unqualified int)) (ordering ())
          (tyvar_map ()) (type_id 173207638) (mem_rep (Closed Bits32))
          (user_type (Abstract (Closed Bits32)))))
        ((closure_mem_rep (Any a)) (closed_args ()) (closed_vars ())))
       Immutable)))

    let g : a has_closure -> int -> int |}]
;;
(* closure type var isn't printed when its generic, this is really int -{a}> int *)
