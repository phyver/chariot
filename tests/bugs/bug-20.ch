data conat_aux('n) where
    | Zero : conat_aux('n)
    | Succ : 'n -> conat_aux('n)

codata conat where
    Dn : conat -> conat_aux(conat)

:set expand_clauses true
:set show_nats false
val test (Dn # 0) = ???
  | test n = ???
