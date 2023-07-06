open! Core

type 'a node = {
  mutable value : 'a option;
  children : 'a node Char.Table.t;
  mutable terminal : bool;
}
[@@deriving sexp]

type 'a t = 'a node Char.Table.t

let create = Char.Table.create

let insert t ~key ~data =
  
