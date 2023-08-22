A simple functional language that aims to blend OCaml and C.

My original idea was for a C like language with a module system like OCaml,
allowing for code reuse. I also enjoy the type system of OCaml, so evanlang2
has a Hindley-Milner type system with full type inference, as well as sum types.

However, the memory model of evanlang2 is much closer to C. This means that functions
must be monomorphized, unlike in OCaml. This also means that higher order functions / partial
application doesn't work quite as nicely. My current semi-solution for this is that there
are two types of functions - raw functions (just a function pointer) and closures, and closures
store along with them information about the memory representation of values it closes over. This
is reasonably similar to C++ and rust which create a unique type for each closure, but it seems
like it is strictly more flexible.

This means that, for instance, two closures that close over values of the same type can be used in the same place, eg.
```
let y = 1 in fun x -> x - y
```
and
```
let y = 1 in fun x -> x + y
```

Additionally, since only the memory representation matters, the following two functions can also
be used in the same place (`@x` means 'get a reference to x', equivalent to `&x` in C, there is a
reason for being unconventional)
```
let y = "hiii" in fun _ -> y
```
and

```
let x = 1 in
let y = @x in
fun _ ->
  let _ = y in
  "result"
```

Currently values can't be polymorphic over different closure/function types, other than closing over
polymorphic values.
