open! Core

module Make (Arg : sig
    type t
  end) =
struct
  type _ Effect.t += Get : Arg.t Effect.t
  type _ Effect.t += Set : Arg.t -> unit Effect.t

  let run_get ~(state : Arg.t ref) ~f =
    Effect.Deep.match_with
      f
      ()
      Effect.Deep.
        { retc = Fn.id
        ; exnc = raise
        ; effc =
            (fun (type b) (e : b Effect.t) ->
              match e with
              | Get -> Some (fun (k : (b, _) continuation) -> continue k !state)
              | _ -> None)
        }
  ;;

  let run_set ~(state : Arg.t ref) ~f =
    Effect.Deep.match_with
      f
      ()
      Effect.Deep.
        { retc = Fn.id
        ; exnc = raise
        ; effc =
            (fun (type a) (e : a Effect.t) ->
              match e with
              | Set state' ->
                state := state';
                Some (fun (k : (a, _) continuation) -> continue k ())
              | _ -> None)
        }
  ;;

  let run ~init ~f =
    let state = ref init in
    run_get ~state ~f:(fun () -> run_set ~state ~f)
  ;;

  let get () = Effect.perform Get
  let set x = Effect.perform (Set x)
end

module Int = Make (Int)

let%expect_test "state test" =
  let f () =
    let x = Int.get () in
    printf "%d\n" x;
    Int.set 10;
    printf "%d\n" (Int.get ())
  in
  Int.run ~f ~init:1;
  [%expect {|
    1
    10 |}]
;;
