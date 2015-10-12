data nat where
    | Zero : nat
    | Succ : nat -> nat

val add : nat -> nat -> nat
  | add m 0 = m
  | add m (n+1) = (add m n) + 1

:set expand_clauses true
val mult : nat -> nat -> nat
  | mult 0 _ = 0
  | mult _ 0 = 0
  | mult m (n+1) = m + (mult m n)

:show mult
