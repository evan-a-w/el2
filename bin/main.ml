open Core
open El2

let make_cmd ~summary ~f =
  let open Command.Let_syntax in
  Command.basic
    ~summary
    [%map_open
      let filename = anon ("filename" %: string) in
      fun () -> f filename]
;;

let compile ~comptime_eval ~keep_temps ~filename ~c_flags =
  let dir = ".build.el2" in
  Core_unix.mkdir_p dir;
  let basename = Filename.basename filename in
  let name = [%string "%{dir}/%{basename}.c"] in
  let chan = Out_channel.create name in
  let has_main =
    Backend.transpile_fully ~for_header:false ~comptime_eval ~chan filename
  in
  let c_flags =
    match has_main with
    | true -> c_flags
    | false -> "-c " ^ c_flags
  in
  Out_channel.close chan;
  let res =
    Core_unix.system [%string "cc -w -o %{basename}.o %{c_flags} %{name}"]
  in
  if not keep_temps
  then ignore @@ Core_unix.system [%string "find %{dir} -delete"];
  match res with
  | Error (`Exit_non_zero i) ->
    failwith [%string "C compiler failed (code %{i#Int})"]
  | Error (`Signal i) ->
    failwith [%string "C compiler failed (signalled %{i#Signal})"]
  | Ok () -> ()
;;

let compile_cmd =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"output C code"
    [%map_open
      let filename = anon ("filename" %: string)
      and c_flags =
        flag
          "flags"
          (optional_with_default "" string)
          ~doc:"string arbitrary flags for cc"
      and skip_comptime_eval =
        flag
          "skip-comptime-eval"
          no_arg
          ~doc:
            "Don't evaluate comptime expressions (can be slow, but sometimes \
             necessary)"
      and keep_temps = flag "keep-tmps" no_arg ~doc:"Keep temporary files" in
      fun () ->
        compile
          ~keep_temps
          ~filename
          ~comptime_eval:(not skip_comptime_eval)
          ~c_flags]
;;

let transpile ~no_format ~for_header ~filename ~comptime_eval =
  let clang_format_exists () =
    Core_unix.system "which clang-format > /dev/null" |> Result.is_ok
  in
  match no_format || not (clang_format_exists ()) with
  | true ->
    (ignore : bool -> unit)
    @@ Backend.transpile_fully
         ~for_header
         ~comptime_eval
         ~chan:Out_channel.stdout
         filename
  | _ ->
    let out_chan = Core_unix.open_process_out "clang-format" in
    (ignore : bool -> unit)
    @@ Backend.transpile_fully
         ~for_header
         ~comptime_eval
         ~chan:out_chan
         filename;
    (match Core_unix.close_process_out out_chan with
     | Ok () -> ()
     | Error _ as e ->
       print_endline
         [%string
           "clang-format failed: %{Core_unix.Exit_or_signal.to_string_hum e}"];
       exit 1)
;;

let transpile_cmd =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"output C code"
    [%map_open
      let filename = anon ("filename" %: string)
      and skip_comptime_eval =
        flag
          "skip-comptime-eval"
          no_arg
          ~doc:"Don't evaluate comptime expressions (can be slow)"
      and no_format = flag "no-format" no_arg ~doc:" Don't format the output"
      and for_header = flag "header" no_arg ~doc:"Make only a header" in
      fun () ->
        transpile
          ~for_header
          ~comptime_eval:(not skip_comptime_eval)
          ~no_format
          ~filename]
;;

let () =
  Command.group
    ~summary:"Operate on evanlang2 files"
    [ "--parse", make_cmd ~summary:"Parse evanlang2" ~f:Frontend.print_ast
    ; ( "--dump-type-state"
      , make_cmd ~summary:"Do some stuff" ~f:Type_check.process_and_dump )
    ; ( "--typed-ast"
      , make_cmd ~summary:"print out the typed ast" ~f:Backend.print_typed_ast )
    ; "--transpile", transpile_cmd
    ; "--compile", compile_cmd
    ]
  |> Command_unix.run
;;
