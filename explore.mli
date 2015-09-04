open Env

val unfold :
  environment ->
  (int -> bool) ->
  (unit, type_expression) unfolded_term ->
  (unit, type_expression) unfolded_term
val unfold_to_depth :
  environment ->
  (empty, unit, type_expression) raw_term ->
  int -> (unit, type_expression) unfolded_term
