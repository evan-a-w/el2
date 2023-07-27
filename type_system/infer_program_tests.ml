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

let rec last = fun x ->
  match x with
  | Cons (x, Nil) -> Some x
  | Cons (_, xs) -> last xs
  | Nil -> None

let list_of_option = fun x ->
  match x with
  | Some x -> Cons (x, Nil)
  | None -> Nil

|}

let run program =
  let action =
    let%bind toplevel_list =
      Parser.try_parse Parser.parse_t program |> State.return
    in
    let%map module_bindings = process_toplevel_list toplevel_list in
    print_s [%message (module_bindings : module_bindings)]
  in
  match State.Result.run action ~state:empty_state with
  | Ok (), _ -> ()
  | Error error, _ -> print_s [%message (error : Sexp.t)]

let%expect_test "program a" =
  run program_a;
  [%expect
    {|
    (module_bindings
     ((toplevel_vars
       ((& ((Forall a (Mono (Lambda (TyVar a) (Pointer (TyVar a)))))))
        (last
         ((Forall j0
           (Mono
            (Lambda
             (Enum ((Unqualified list) ((a (TyVar j0))) 1)
              ((Cons
                ((Tuple
                  ((TyVar j0)
                   (Recursive_constructor
                    ((Unqualified list) ((a (TyVar j0))) 0))))))
               (Nil ())))
             (Enum ((Unqualified option) ((a (TyVar j0))) 1)
              ((Some ((TyVar j0))) (None ()))))))
          (Mono (TyVar a0))))
        (list_of_option
         ((Forall q0
           (Mono
            (Lambda
             (Enum ((Unqualified option) ((a (TyVar q0))) 1)
              ((Some ((TyVar q0))) (None ())))
             (Enum ((Unqualified list) ((a (TyVar q0))) 1)
              ((Cons
                ((Tuple
                  ((TyVar q0)
                   (Recursive_constructor
                    ((Unqualified list) ((a (TyVar q0))) 0))))))
               (Nil ()))))))))))
      (toplevel_records ())
      (toplevel_constructors
       ((Cons
         (((Forall a
            (Mono
             (Tuple
              ((TyVar a)
               (Recursive_constructor ((Unqualified list) ((a (TyVar a))) 0)))))))
          (Forall a
           (Mono
            (Enum ((Unqualified list) ((a (TyVar a))) 1)
             ((Cons
               ((Tuple
                 ((TyVar a)
                  (Recursive_constructor ((Unqualified list) ((a (TyVar a))) 0))))))
              (Nil ())))))))
        (Error
         (((Forall b (Mono (TyVar b))))
          (Forall b
           (Forall a
            (Mono
             (Enum ((Unqualified result) ((a (TyVar a)) (b (TyVar b))) 1)
              ((Ok ((TyVar a))) (Error ((TyVar b))))))))))
        (Nil
         (()
          (Forall a
           (Mono
            (Enum ((Unqualified list) ((a (TyVar a))) 1)
             ((Cons
               ((Tuple
                 ((TyVar a)
                  (Recursive_constructor ((Unqualified list) ((a (TyVar a))) 0))))))
              (Nil ())))))))
        (None
         (()
          (Forall a
           (Mono
            (Enum ((Unqualified option) ((a (TyVar a))) 1)
             ((Some ((TyVar a))) (None ())))))))
        (Ok
         (((Forall a (Mono (TyVar a))))
          (Forall b
           (Forall a
            (Mono
             (Enum ((Unqualified result) ((a (TyVar a)) (b (TyVar b))) 1)
              ((Ok ((TyVar a))) (Error ((TyVar b))))))))))
        (Some
         (((Forall a (Mono (TyVar a))))
          (Forall a
           (Mono
            (Enum ((Unqualified option) ((a (TyVar a))) 1)
             ((Some ((TyVar a))) (None ())))))))))
      (toplevel_type_constructors
       ((list
         ((Single_arg Invariant a) list
          (Enum ((Unqualified list) ((a (TyVar a))) 1)
           ((Cons
             ((Tuple
               ((TyVar a)
                (Recursive_constructor ((Unqualified list) ((a (TyVar a))) 0))))))
            (Nil ())))))
        (option
         ((Single_arg Invariant a) option
          (Enum ((Unqualified option) ((a (TyVar a))) 1)
           ((Some ((TyVar a))) (None ())))))
        (result
         ((Tuple_arg ((Invariant a) (Invariant b))) result
          (Enum ((Unqualified result) ((a (TyVar a)) (b (TyVar b))) 1)
           ((Ok ((TyVar a))) (Error ((TyVar b)))))))))
      (toplevel_types
       ((bool (Abstract ((Unqualified bool) () 0)))
        (char (Abstract ((Unqualified char) () 0)))
        (float (Abstract ((Unqualified float) () 0)))
        (int (Abstract ((Unqualified int) () 0)))
        (string (Abstract ((Unqualified string) () 0)))
        (unit (Abstract ((Unqualified unit) () 0)))))
      (toplevel_modules ()) (opened_modules ()))) |}]
