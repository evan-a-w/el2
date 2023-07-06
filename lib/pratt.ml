open! Core

(* https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html *)
(* https://v2.ocaml.org/api/Ocaml_operators.html *)

(* (left, right) *)
let function_application_binding_power = (98, 99)
let unary_prefix_binding_power = [ ("!", 100); ("~", 100) ]
let binary_prefix_binding_power = [ ("!", 100); ("~", 100) ]
let parse : Ast.node -> Ast.node = Fn.id
