open Env

val process_function_defs :
  environment ->
  (var_name * type_expression option * (parsed_term * parsed_term) list) list ->
  environment
