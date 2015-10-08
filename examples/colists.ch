-- we need a sum (data) for the constructors of possibly infinite natural numbers
data conat_aux('n) where
    | Zero : conat_aux('n)
    | Succ : 'n -> conat_aux('n)

-- possibly infinite natural numbers
codata conat where
    Dn : conat -> conat_aux(conat)

val add : conat -> conat -> conat
  | add m (Dn # 0) = m
  | add m (Dn # (n+1)) = Dn # ((add m n) + 1)

-- some care is needed to define multiplication so that the totality test passes
--   - we cannot add infinitely many 0s => special case
--   - we need to explicitly add the Succ constructor so that the tests sees
--     the definition is productive (it wouldn't be necessary with PML's flow analysis)
val one = Dn # Succ $ Dn # 0
val infinity = Dn # Succ infinity

val mult : conat -> conat -> conat
  | mult (Dn # 0) _ = one
  | mult _ (Dn # 0) = one
  | mult (Dn # m+1) (Dn # (n+1)) = m + (Dn # (mult (Dn # m+1) n) + 1)

-- substraction isn't total: sub infinity infinity is undefined...
val sub : conat -> conat -> conat
  | sub m (Dn # 0) = m
  | sub (Dn # 0) _ = Dn # 0
  | sub (Dn # m+1) (Dn # n+1) = sub m n         -- this is not productive


-- we need a sum (data) for the constructors of possibly infinite lists
data colist_aux('x,'l) where
    | Nil : colist_aux('x,'l)
    | Cons : 'x -> 'l -> colist_aux('x,'l)

-- possibly infinite lists
codata colist('x) where
    Dl : colist('x) -> colist_aux('x,colist('x))

-- length of a colist: it can be infinite
val colength : colist('x) -> conat
  | colength (Dl # []) = Dn # 0
  | colength (Dl # _::l) = Dn # (colength l)+1

val arith n r = Dl # n::(arith (add n r) r)
