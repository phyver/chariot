open Env

val is_exhaustive :
  var_name -> var_name list -> 'v case_struct_tree -> bool

val convert_cs_to_clauses :
  var_name ->
  var_name list ->
  (empty, 'p, type_expression) raw_term case_struct_tree ->
  ((empty, unit, unit) raw_term * (empty, 'p, unit) raw_term) list

val case_struct_of_clauses :
  environment ->
  var_name ->
  type_expression ->
  ((empty, 'p, type_expression) raw_term *
   (empty, 'p, type_expression) raw_term) list ->
  var_name *
  ((empty, 'p, type_expression) raw_term *
   (empty, 'p, type_expression) raw_term) list *
  var_name list *
  (empty, unit, type_expression) raw_term case_struct_tree
