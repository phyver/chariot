open Env

val remove_struct_defs :
  (var_name * type_expression option *
   (parsed_term * parsed_term) list)
  list ->
  (var_name * type_expression option *
   (plain_term * plain_term) list)
  list
