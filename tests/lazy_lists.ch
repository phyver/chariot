:set show_priorities false

(* type of natural numbers *)
data nat where Zero : nat | Succ : nat -> nat

(* addition of natural numbers *)
val add : nat -> nat -> nat
    | add n 0 = n
    | add n (m+1) = Succ (add n m)

val mult : nat -> nat -> nat
    | mult n 0 = 0
    | mult n (m+1) = n + (mult n m)

val pow : nat -> nat -> nat
    | pow n 0 = 1
    | pow n (m+1) = mult n (pow n m)


data list_aux('a,'l) where Nil : list_aux('a,'l) | Cons : 'a -> 'l -> list_aux('a,'l)

codata colist('a) where Unfreeze : colist('a) -> list_aux('a,colist('a))

val freeze : list_aux('a,colist('a)) -> colist('a)
  | (freeze x).Unfreeze = x

val
    (map f s).Unfreeze = map_aux f s.Unfreeze
and
    | map_aux f (Nil) = Nil
    | map_aux f (Cons x s) = Cons (f x) (map f s)

val zeros.Unfreeze = Cons 0 zeros

val (incr n).Unfreeze = Cons n (incr (n+1))

val   (decr 0).Unfreeze = Nil
    | (decr (n+1)).Unfreeze = Cons n (decr n)

:reduce incr 10

:reduce decr 10

:unfold incr 10, 5

:unfold incr 10, 12

:unfold decr 10, 5

:unfold decr 10, 10

:unfold decr 10, 20










