type ('go, 'state, 'stop) t = Go of ('state -> 'go * 'state) | Stop of 'stop

val return : 'go -> ('go, 'state, 'stop) t
val stop : 'stop -> ('go, 'state, 'stop) t
val run_state : ('go, 'state, 'stop) t -> 'state -> 'go * 'state
val get : ('state, 'state, 'stop) t
val put : 'state -> (unit, 'state, 'stop) t

val bind :
  ('go, 'state, 'stop) t ->
  ('go -> ('go', 'state, 'stop) t) ->
  ('go', 'state, 'stop) t
