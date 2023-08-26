open! Core
open! Infer
open! Ty
open! Shared
open! Frontend
open! State.Result.Let_syntax
open! Infer_expr_tests

let%expect_test "single_arg_no_closed" =
  infer_and_print_mono
    ~print_state:false
    ~programs:[ {| let val = fun a -> a in val |} ];
  [%expect {| b0 -> b0 |}]
;;

let%expect_test "single_arg_closed_int" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {| let x = 1 in
           let val = fun () -> x in
           val |} ];
  [%expect {| unit -{int}> int |}]
;;

let%expect_test "two_arg_no_extra" =
  infer_and_print_mono
    ~print_state:false
    ~programs:[ {| let val = fun a b -> a in val |} ];
  [%expect {| d0 -> c0 -{d0}> d0 |}]
;;

let%expect_test "two_arg_and_closed_outer" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {| let outer = "hi" in
           let val = fun a b -> outer
           in val |}
      ];
  [%expect {| d0 -{string}> c0 -{string}> string |}]
;;

let%expect_test "rec_single_arg_no_closed" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {|
       let (-) = fun (a : int) (b : int) -> a in
       let (=) = fun (a : int) (b : int) -> true in
       let rec get_to_zero = fun a ->
         if a = 0 then a else get_to_zero (a - 1)
       in get_to_zero |}
      ];
  [%expect {| int -> int |}]
;;

let%expect_test "two_arg_and_closed_inner" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {| let outer = "hi" in
           let val = fun a ->
             let y = 1 in
             fun b ->
               let _ = y in outer
           in val |}
      ];
  [%expect {| d0 -{string}> c0 -{int|string}> string |}]
;;

let%expect_test "list map" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {|
        let rec map = fun f x ->
          match x with
          | Nil -> Nil
          | Cons (x, xs) -> Cons (f x, map f xs) in
        map
        |}
      ];
  [%expect {| (m0 -> l0) -> m0 list -> l0 list |}]
;;

let%expect_test "list map generic" =
  infer_and_print_mono
    ~print_state:false
    ~programs:
      [ {|
        let outer = "hi" in
        let a = fun x -> outer in
        let b = fun x -> "hi" in
        let list = Cons (1, Cons (2, Nil)) in
        let rec map = fun f x ->
          match x with
          | Nil -> Nil
          | Cons (x, xs) -> Cons (f x, map f xs) in
        (map a list, map b list)
        |}
      ];
  [%expect {| (string list, string list) |}]
;;
