open Env

val reset_fresh_variable_generator :
  type_expression list ->
    unit

val instantiate_type :
  type_expression ->
    type_expression

val unify_type_mgu :
  type_expression ->
  type_expression ->
    type_substitution

val equal_type :
  type_expression ->
  type_expression ->
    bool

val infer_type_term :
  environment ->
  (empty, 'p, 't) raw_term ->
      type_expression * (empty, 'p, type_expression) raw_term * (var_name * type_expression) list

val infer_type_clause :
  environment ->
  (var_name * type_expression) list ->
  (empty, 'p, 't) raw_term ->
  (empty, 'p, 't) raw_term ->
      (var_name * type_expression) list *
      (empty, 'p, type_expression) raw_term *
      (empty, 'p, type_expression) raw_term

val infer_type_defs :
  environment ->
  (var_name * type_expression option * ((empty, 'p, 't) raw_term * (empty, 'p, 't) raw_term) list) list ->
      (var_name * type_expression * ((empty, 'p, type_expression) raw_term * (empty, 'p, type_expression) raw_term) list) list
