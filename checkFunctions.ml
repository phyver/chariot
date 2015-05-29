open Base
open Misc

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression * (term list * term) list) list)
  = env
