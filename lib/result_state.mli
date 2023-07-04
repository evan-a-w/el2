type ('go, 'stop) result = Go of 'go | Stop of 'stop [@@deriving sexp]
type ('go, 'stop, 'state) t [@@deriving sexp]

val stop : 'stop -> ('go, 'stop, 'state) t
val run : ('go, 'stop, 'state) t -> state:'state -> ('go, 'stop) result * 'state
val get : ('state, 'stop, 'state) t
val put : 'state -> (unit, 'stop, 'state) t
val ( >>= ) : ('a, 'd, 'e) t -> ('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
val ( >>| ) : ('a, 'd, 'e) t -> ('a -> 'b) -> ('b, 'd, 'e) t

module Let_syntax : sig
  val return : 'a -> ('a, 'b, 'c) t
  val ( >>= ) : ('a, 'd, 'e) t -> ('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
  val ( >>| ) : ('a, 'd, 'e) t -> ('a -> 'b) -> ('b, 'd, 'e) t

  module Let_syntax : sig
    val return : 'a -> ('a, 'b, 'c) t
    val bind : ('a, 'd, 'e) t -> f:('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
    val map : ('a, 'd, 'e) t -> f:('a -> 'b) -> ('b, 'd, 'e) t
    val both : ('a, 'd, 'e) t -> ('b, 'd, 'e) t -> ('a * 'b, 'd, 'e) t

    module Open_on_rhs : sig end
  end
end

module Monad_infix : sig
  val ( >>= ) : ('a, 'd, 'e) t -> ('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
  val ( >>| ) : ('a, 'd, 'e) t -> ('a -> 'b) -> ('b, 'd, 'e) t
end

val bind : ('a, 'd, 'e) t -> f:('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
val return : 'a -> ('a, 'b, 'c) t
val map : ('a, 'd, 'e) t -> f:('a -> 'b) -> ('b, 'd, 'e) t
val join : (('a, 'd, 'e) t, 'd, 'e) t -> ('a, 'd, 'e) t
val ignore_m : ('a, 'd, 'e) t -> (unit, 'd, 'e) t
val all : ('a, 'd, 'e) t list -> ('a list, 'd, 'e) t
val all_unit : (unit, 'd, 'e) t list -> (unit, 'd, 'e) t
