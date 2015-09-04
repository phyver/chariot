open Env

val reduce :
  environment ->
  (empty, unit, type_expression) raw_term ->
  (empty, unit, type_expression) raw_term
