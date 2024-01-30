open! Core

type t = (int ref[@ignore]) [@@deriving sexp, compare, hash, equal]

let create () = ref 0

let next_int t =
  let res = !t in
  incr t;
  res
;;

let next_num t =
  let res = !t in
  incr t;
  Int.to_string res
;;

let next_alphabetical t =
  let i = next_int t in
  let char, rest = i % 26, i / 26 in
  [%string {|%{"abcdefghijklmnopqrstuvwxyz".[char]#Char}%{rest#Int}|}]
;;
