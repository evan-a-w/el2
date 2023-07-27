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
             (Enum
              ((type_name (Unqualified list)) (ordering ())
               (tyvar_map ((a (TyVar j0)))) (level 1))
              ((Cons
                ((Tuple
                  ((TyVar j0)
                   (Recursive_constructor
                    ((type_name (Unqualified list)) (ordering ((a)))
                     (tyvar_map ((a (TyVar j0)))) (level 0)))))))
               (Nil ())))
             (Enum
              ((type_name (Unqualified option)) (ordering ())
               (tyvar_map ((a (TyVar j0)))) (level 1))
              ((Some ((TyVar j0))) (None ()))))))
          (Mono (TyVar a0))))
        (list_of_option
         ((Forall q0
           (Mono
            (Lambda
             (Enum
              ((type_name (Unqualified option)) (ordering ((a)))
               (tyvar_map ((a (TyVar q0)))) (level 1))
              ((Some ((TyVar q0))) (None ())))
             (Enum
              ((type_name (Unqualified list)) (ordering ())
               (tyvar_map ((a (TyVar q0)))) (level 1))
              ((Cons
                ((Tuple
                  ((TyVar q0)
                   (Recursive_constructor
                    ((type_name (Unqualified list)) (ordering ((a)))
                     (tyvar_map ((a (TyVar q0)))) (level 0)))))))
               (Nil ()))))))))
        (x
         ((Mono
           (Abstract
            ((type_name (Unqualified int)) (ordering ()) (tyvar_map ())
             (level 0))))))))
      (toplevel_records ())
      (toplevel_constructors
       ((Cons
         (((Forall a
            (Mono
             (Tuple
              ((TyVar a)
               (Recursive_constructor
                ((type_name (Unqualified list)) (ordering ((a)))
                 (tyvar_map ((a (TyVar a)))) (level 0))))))))
          (Forall a
           (Mono
            (Enum
             ((type_name (Unqualified list)) (ordering ())
              (tyvar_map ((a (TyVar a)))) (level 1))
             ((Cons
               ((Tuple
                 ((TyVar a)
                  (Recursive_constructor
                   ((type_name (Unqualified list)) (ordering ((a)))
                    (tyvar_map ((a (TyVar a)))) (level 0)))))))
              (Nil ())))))))
        (Error
         (((Forall b (Mono (TyVar b))))
          (Forall b
           (Forall a
            (Mono
             (Enum
              ((type_name (Unqualified result)) (ordering ())
               (tyvar_map ((a (TyVar a)) (b (TyVar b)))) (level 1))
              ((Ok ((TyVar a))) (Error ((TyVar b))))))))))
        (Nil
         (()
          (Forall a
           (Mono
            (Enum
             ((type_name (Unqualified list)) (ordering ())
              (tyvar_map ((a (TyVar a)))) (level 1))
             ((Cons
               ((Tuple
                 ((TyVar a)
                  (Recursive_constructor
                   ((type_name (Unqualified list)) (ordering ((a)))
                    (tyvar_map ((a (TyVar a)))) (level 0)))))))
              (Nil ())))))))
        (None
         (()
          (Forall a
           (Mono
            (Enum
             ((type_name (Unqualified option)) (ordering ())
              (tyvar_map ((a (TyVar a)))) (level 1))
             ((Some ((TyVar a))) (None ())))))))
        (Ok
         (((Forall a (Mono (TyVar a))))
          (Forall b
           (Forall a
            (Mono
             (Enum
              ((type_name (Unqualified result)) (ordering ())
               (tyvar_map ((a (TyVar a)) (b (TyVar b)))) (level 1))
              ((Ok ((TyVar a))) (Error ((TyVar b))))))))))
        (Some
         (((Forall a (Mono (TyVar a))))
          (Forall a
           (Mono
            (Enum
             ((type_name (Unqualified option)) (ordering ())
              (tyvar_map ((a (TyVar a)))) (level 1))
             ((Some ((TyVar a))) (None ())))))))))
      (toplevel_type_constructors
       ((list
         ((Single_arg Invariant a) list
          (Enum
           ((type_name (Unqualified list)) (ordering ((a)))
            (tyvar_map ((a (TyVar a)))) (level 1))
           ((Cons
             ((Tuple
               ((TyVar a)
                (Recursive_constructor
                 ((type_name (Unqualified list)) (ordering ((a)))
                  (tyvar_map ((a (TyVar a)))) (level 0)))))))
            (Nil ())))))
        (option
         ((Single_arg Invariant a) option
          (Enum
           ((type_name (Unqualified option)) (ordering ((a)))
            (tyvar_map ((a (TyVar a)))) (level 1))
           ((Some ((TyVar a))) (None ())))))
        (result
         ((Tuple_arg ((Invariant a) (Invariant b))) result
          (Enum
           ((type_name (Unqualified result)) (ordering ((a b)))
            (tyvar_map ((a (TyVar a)) (b (TyVar b)))) (level 1))
           ((Ok ((TyVar a))) (Error ((TyVar b)))))))))
      (toplevel_types
       ((bool
         (Abstract
          ((type_name (Unqualified bool)) (ordering ()) (tyvar_map ()) (level 0))))
        (char
         (Abstract
          ((type_name (Unqualified char)) (ordering ()) (tyvar_map ()) (level 0))))
        (float
         (Abstract
          ((type_name (Unqualified float)) (ordering ()) (tyvar_map ())
           (level 0))))
        (int
         (Abstract
          ((type_name (Unqualified int)) (ordering ()) (tyvar_map ()) (level 0))))
        (list
         (Enum
          ((type_name (Unqualified list)) (ordering ((a)))
           (tyvar_map ((a (TyVar a)))) (level 1))
          ((Cons
            ((Tuple
              ((TyVar a)
               (Recursive_constructor
                ((type_name (Unqualified list)) (ordering ((a)))
                 (tyvar_map ((a (TyVar a)))) (level 0)))))))
           (Nil ()))))
        (option
         (Enum
          ((type_name (Unqualified option)) (ordering ((a)))
           (tyvar_map ((a (TyVar a)))) (level 1))
          ((Some ((TyVar a))) (None ()))))
        (result
         (Enum
          ((type_name (Unqualified result)) (ordering ((a b)))
           (tyvar_map ((a (TyVar a)) (b (TyVar b)))) (level 1))
          ((Ok ((TyVar a))) (Error ((TyVar b))))))
        (string
         (Abstract
          ((type_name (Unqualified string)) (ordering ()) (tyvar_map ())
           (level 0))))
        (unit
         (Abstract
          ((type_name (Unqualified unit)) (ordering ()) (tyvar_map ()) (level 0))))))
      (toplevel_modules ()) (opened_modules ()))) |}]
