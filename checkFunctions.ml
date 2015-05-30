open Base
open Misc

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression * (term * term) list) list)
  = env
