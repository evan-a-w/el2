open! Core

(* https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html *)
(* https://v2.ocaml.org/api/Ocaml_operators.html *)

module Associativity = struct
  type t = [ `Left | `Right ] [@@deriving sexp, compare, equal, hash]
end

module Operator_type = struct
  type t = Unary | Binary [@@deriving sexp, compare, equal, hash]
end

module Match_type = struct
  type t = Full | Prefix [@@deriving sexp, compare, equal, hash]
end

module Match_info = struct
  type t = { binding_power : int; associativity : Associativity.t }
  [@@deriving sexp, equal, compare, hash]
end

module Trie = struct
  module Match_table = Hashtbl.Make (struct
    type t = Operator_type.t * Match_type.t
    [@@deriving sexp, compare, equal, hash]
  end)

  type node = {
    children : node Char.Table.t;
    matches : Match_info.t Match_table.t;
  }

  let create_node () =
    { children = Char.Table.create (); matches = Match_table.create () }

  type t = { children : node Char.Table.t; mutable bp_counter : int }

  let empty () = { children = Char.Table.create (); bp_counter = 100 }

  let get_bp t ~operator_type =
    let dec =
      match operator_type with Operator_type.Unary -> 1 | Binary -> 2
    in
    let res = t.bp_counter in
    t.bp_counter <- t.bp_counter - dec;
    res

  let _insert t ~operator_type ~associativity ~match_type ~operator
      ~binding_power =
    let rec insert_node node ~chars =
      match chars () with
      | Stdlib.Seq.Nil ->
          Match_table.add_exn node.matches
            ~key:(operator_type, match_type)
            ~data:{ binding_power; associativity }
      | Cons (c, chars) ->
          let child =
            Char.Table.find_or_add node.children c ~default:create_node
          in
          insert_node child ~chars
    in
    let chars = Stdlib.String.to_seq operator in
    match chars () with
    | Nil -> ()
    | Cons (c, chars) ->
        let child = Char.Table.find_or_add t.children c ~default:create_node in
        insert_node child ~chars

  let insert_binary t ~associativity =
    _insert t ~operator_type:Binary ~associativity

  let insert_unary t = _insert t ~operator_type:Unary ~associativity:`Left

  let search t ~operator_type ~operator =
    let rec search_node node ~chars =
      match chars () with
      | Stdlib.Seq.Nil -> (
          match
            Match_table.find node.matches (operator_type, Match_type.Full)
          with
          | Some _ as res -> res
          | None -> Match_table.find node.matches (operator_type, Prefix))
      | Cons (c, chars) -> (
          match Match_table.find node.matches (operator_type, Prefix) with
          | Some _ as res -> res
          | None -> (
              match Char.Table.find node.children c with
              | None -> None
              | Some child -> search_node child ~chars))
    in
    let chars = Stdlib.String.to_seq operator in
    match chars () with
    | Nil -> None
    | Cons (c, chars) -> (
        match Char.Table.find t.children c with
        | None -> None
        | Some child -> search_node child ~chars)
end

let function_bp = ref 0

let bp_map =
  let trie = Trie.empty () in
  let data =
    [|
      (`Unary, Match_type.Prefix, [| "!"; "~" |]);
      (`Left, Prefix, [| "#" |]);
      (`Unary, Match_type.Full, [| "-"; "-." |]);
      (`Right, Prefix, [| "**" |]);
      (`Left, Prefix, [| "*"; "/"; "%" |]);
      (`Left, Prefix, [| "+"; "-" |]);
      (`Right, Prefix, [| "@"; "^" |]);
      (`Left, Prefix, [| "="; "<"; ">"; "|"; "&"; "$"; "!=" |]);
      (`Right, Full, [| "&"; "&&" |]);
      (`Right, Full, [| "||" |]);
      (`Right, Full, [| "<-"; ":=" |]);
    |]
  in
  Array.iter data ~f:(fun (associativity, match_type, operators) ->
      let operator_type =
        match associativity with
        | `Unary -> Operator_type.Unary
        | `Left | `Right -> Binary
      in
      let binding_power = Trie.get_bp trie ~operator_type in
      Array.iter operators ~f:(fun operator ->
          (match operator with
          | "#" -> function_bp := Trie.get_bp trie ~operator_type:Binary
          | _ -> ());
          match associativity with
          | `Unary ->
              Trie.insert_unary trie ~operator ~binding_power ~match_type
          | (`Left | `Right) as associativity ->
              Trie.insert_binary trie ~operator ~associativity ~match_type
                ~binding_power));
  trie

let infix_binding_power ~operator =
  match Trie.search bp_map ~operator_type:Binary ~operator with
  | Some { binding_power; associativity } -> (
      match associativity with
      | `Left -> Some (binding_power, binding_power + 1)
      | `Right -> Some (binding_power + 1, binding_power))
  | None -> None

let infix_function_binding_power = !function_bp

let prefix_binding_power ~operator =
  match Trie.search bp_map ~operator_type:Unary ~operator with
  | Some { binding_power; _ } -> Some binding_power
  | None -> None
