open! Core

let counter = ref 1

let init () = counter := 1

let gen () =
  let i = !counter in
  counter := i + 1;
  let letter = Char.of_int_exn (Char.to_int 'a' + (i mod 26)) in
  let s = String.make 1 letter ^ Int.to_string (i / 26) in
  s
