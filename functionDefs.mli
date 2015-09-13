open Env

val process_function_defs :
  environment ->
  (var_name * type_expression option * (plain_term * plain_term) list) list ->
  environment
