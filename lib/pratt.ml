open! Core

(* https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html *)
(* https://v2.ocaml.org/api/Ocaml_operators.html *)

module Associativity = struct
  type t = Left | Right [@@deriving sexp, compare, equal]
end

module Operator_type = struct
  type t = Unary | Binary [@@deriving sexp, compare, equal, hash]
end

module Match_type = struct
  type t = Full | Prefix [@@deriving sexp, compare, equal, hash]
end

module Trie = struct
  type match_info = { binding_power : int; associativity : Associativity.t }

  module Match_table = Hashtbl.Make (struct
    type t = Operator_type.t * Match_type.t
    [@@deriving sexp, compare, equal, hash]
  end)

  type node = {
    is_end : bool;
    children : node Char.Table.t;
    matches : match_info Match_table.t;
  }

  type t = { children : node Char.Table.t; mutable bp_counter : int }

  let empty () = { children = Char.Table.create (); bp_counter = 100 }

  let get_bp t ~operator_type ~decrement_bp =
    let dec = match decrement_bp, operator_type with false, _ -> 0 | _, Operator_type.Unary -> 1 | _, Binary -> 2 in
    let res = t.bp_counter in
    t.bp_counter <- t.bp_counter - dec;
    res

  let insert ?(associativity=Associativity.Left) t  ~operator_type ~match_type ~operator ~decrement_bp =
    let rec insert_node node ~chars =
      match Sequence.next chars with
      | None -> (
          Match_table.add_exn node.matches ~key:(operator_type, match_type)
            ~data:{ binding_power = get_bp t ~operator_type ~decrement_bp; associativity };
      )
    in
end

(* (left, right) *)
let function_application_binding_power = 99
let unary_prefix_binding_power = [| ("!", 100); ("~", 100); ("-", 98) |]

let binary_prefix_binding_power =
  [|
    ([| "**"; "<<"; ">>" |], Right);
    ([| "*"; "/"; "%" |], Left);
    ([| "+"; "-" |], Left);
    ([| "@"; "^" |], Right);
    ([| "="; "<"; ">"; "|"; "&"; "$"; "!=" |], Left);
  |]

let parse : Ast.node -> Ast.node = Fn.id
