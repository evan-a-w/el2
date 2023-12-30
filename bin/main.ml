open Core
open El2


let make_cmd ~summary ~f =
  Command.basic_spec
    ~summary
    Command.Spec.(empty +> anon ("filename" %: string))
    (Frontend.do_stuff ~f)
;;

let () =
  Command.group
    ~summary:"Operate on evanlang2 files"
    [ "--parse", make_cmd ~summary:"Parse evanlang2" ~f:Frontend.print_ast
    ; ( "--dump-type-state"
      , make_cmd ~summary:"Do some stuff" ~f:Type_check.process_and_dump )
    ; ( "--typed-ast"
      , make_cmd ~summary:"print out the typed ast" ~f:Backend.print_typed_ast )
    ; "--compile", make_cmd ~summary:"compile" ~f:Backend.compile_fully
    ]
  |> Command_unix.run
;;
