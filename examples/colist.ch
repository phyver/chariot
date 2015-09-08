data conat_aux('n) where Zero : conat_aux('n) | Succ : 'n -> conat_aux('n)

codata conat where Dn : conat -> conat_aux(conat)

data colist_aux('x,'l) where Nil : colist_aux('x,'l) | Cons : 'x -> 'l -> colist_aux('x,'l)

codata colist('x) where Dl : colist('x) -> colist_aux('x,colist('x))

:set show_nats false
val colength : colist('x) -> conat
  | colength (Dl # Nil) = Dn # Zero
  | colength (Dl # Cons _ l) = Dn # Succ (colength l)


val inf = Dl # Cons (Dn # 0) inf
