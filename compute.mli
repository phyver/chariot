open Env

val reduce :
  environment ->
  (empty, 'p, 't) raw_term ->
    computed_term

val unfold :
  environment ->
  (int -> bool) ->
  explore_term ->
    explore_term

val unfold_to_depth :
  environment ->
  typed_term ->
  int ->
    explore_term
