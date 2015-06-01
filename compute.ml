open Base

let unify_pattern (pattern:term) (u:term) : (var_name*term) list
  = assert false

let subst_term (u:term) (sigma:(var_name*term) list) : term
  = assert false

let reduce_head (env:environment) (u:term) : term
  = assert false

let reduce_leftmost (env:environment) (u:term) : term
  = assert false

let reduce_all (env:environment) (u:term) : term
  = assert false
