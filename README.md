A simple (and incomplete) language that aims to blend OCaml and C.

My original idea was for a C like language with a module system like OCaml,
allowing for code reuse. I also enjoy the type system of OCaml, so el2
has a Hindley-Milner type system with full type inference, as well as sum types/tagged unions.

Currently, the module system is unimplemented - the language is basically (a less complete) C with type inference and some other nice stuff like the order of declarations not being important.
In fact, it even compiles to C (though I hope to use LLVM in the future).

Usage:
Install ocaml (opam, dune etc.)
`dune exec bin/main.exe -- --comp <filename>` will spit out C code for you to separately compile.

The compilation error messages are absolutely awful, worse than you can imagine.

```
[*
  this is a comment
*]

[* sum type/enum taking a type variable 'a' *]
type option(a) :=
  | Some(a)
  | None

[* product type/struct, also with a variable *]
type list(a) :=
  { data : a;
    next : option(&(list(a)))
  }

[* type without any type args *]
type unused_data := { unused_data : unit }

let do_nothing(a) := ()

let option_iter(a, f) := {
  [* pattern matching *]
  match a with
  | Some(a) -> f(a)
  | None -> ()
}

let list_option_iter(
  a,
  [* can optionally declare the type of arguments *]
  f : &char -> c_int
) := {

  option_iter(a, do_nothing);

  match a with
  | None -> ()
  | Some(a) -> {
        [* deref, same as C *]
        f((*a).data);

        [* postfix deref, equivalent to the above *]
        f(a^.data);

        list_option_iter(a^.next, f)
    }
}

[* optional type declaration of return type
   the double meaning of ':=' and ': type_expr ='
   was stolen from jai i think
*]
let main() : i64 = {
  [* you have to name the struct when creating one *]
  let first := #list {
    data : "first";
    next : None
  };

  [* type declarations can be used in the same way for local variables *]
  let second : list(&char) = #list {
    data : "second";
    next : Some(&first)
  };

  let unused := second.next;

  list_option_iter(Some(&second), print_endline);
  0
}
[* SUA PUA *]

[* declares a function that is linked already (in the C standard library) *]
implicit_extern print_endline : &char -> c_int = "puts"
```
