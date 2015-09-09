open Env

val infer_priorities :
  environment ->
  (var_name * type_expression * (typed_term*typed_term) list * 'x) list ->
  (var_name * type_expression * (term*term) list * 'x) list
