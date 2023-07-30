type ('a, 'state) t = 'state -> 'a * 'state [@@deriving sexp]

val run : ('a, 'b) t -> state:'b -> 'a * 'b
val get : 'a -> 'a * 'a
val put : 'state -> (unit, 'state) t
val ( >>= ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
val ( >>| ) : ('a, 'e) t -> ('a -> 'b) -> ('b, 'e) t
val modify : ('state -> 'state) -> (unit, 'state) t

module Let_syntax : sig
  val return : 'a -> ('a, 'b) t
  val ( >>= ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
  val ( >>| ) : ('a, 'e) t -> ('a -> 'b) -> ('b, 'e) t

  module Let_syntax : sig
    val return : 'a -> ('a, 'b) t
    val bind : ('a, 'e) t -> f:('a -> ('b, 'e) t) -> ('b, 'e) t
    val map : ('a, 'e) t -> f:('a -> 'b) -> ('b, 'e) t
    val both : ('a, 'e) t -> ('b, 'e) t -> ('a * 'b, 'e) t

    module Open_on_rhs : sig end
  end
end

module Monad_infix : sig
  val ( >>= ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
  val ( >>| ) : ('a, 'e) t -> ('a -> 'b) -> ('b, 'e) t
end

val bind : ('a, 'e) t -> f:('a -> ('b, 'e) t) -> ('b, 'e) t
val return : 'a -> ('a, 'b) t
val map : ('a, 'e) t -> f:('a -> 'b) -> ('b, 'e) t
val join : (('a, 'e) t, 'e) t -> ('a, 'e) t
val ignore_m : ('a, 'e) t -> (unit, 'e) t
val all : ('a, 'e) t list -> ('a list, 'e) t
val all_unit : (unit, 'e) t list -> (unit, 'e) t

module Result : sig
  type nonrec ('a, 'error, 'state) t = (('a, 'error) Result.t, 'state) t
  [@@deriving sexp]

  val error : 'stop -> ('go, 'stop, 'state) t

  val run :
    ('go, 'stop, 'state) t -> state:'state -> ('go, 'stop) result * 'state

  val get : ('state, 'stop, 'state) t
  val put : 'state -> (unit, 'stop, 'state) t
  val first : ('a, 'error, 'state) t list -> ('a, 'error list, 'state) t
  val t_of_state : ('state -> 'a * 'state) -> ('a, 'error, 'state) t
  val ( >>= ) : ('a, 'd, 'e) t -> ('a -> ('b, 'd, 'e) t) -> ('b, 'd, 'e) t
  val ( >>| ) : ('a, 'd, 'e) t -> ('a -> 'b) -> ('b, 'd, 'e) t
  val ( <|> ) : ('a, 'd, 'e) t -> ('a, 'd, 'e) t -> ('a, 'd, 'e) t
  val modify : ('state -> 'state) -> (unit, 'stop, 'state) t

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

  val map_error :
    ('a, 'error, 'state) t -> f:('error -> 'error') -> ('a, 'error', 'state) t

  val join : (('a, 'd, 'e) t, 'd, 'e) t -> ('a, 'd, 'e) t
  val ignore_m : ('a, 'd, 'e) t -> (unit, 'd, 'e) t
  val all : ('a, 'd, 'e) t list -> ('a list, 'd, 'e) t
  val all_unit : (unit, 'd, 'e) t list -> (unit, 'd, 'e) t
end
