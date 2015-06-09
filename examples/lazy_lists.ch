
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


data stream_aux('a,'s) where Cons : 'a -> 's -> stream_aux('a,'s)

codata stream('a) where Unfreeze : stream('a) -> stream_aux('a,stream('a))

val freeze : stream_aux('a,stream('a)) -> stream('a)
  | (freeze x).Unfreeze = x

val (map f s).Unfreeze = map_aux f s.Unfreeze
and map_aux f (Cons x s) = Cons (f x) (map f s)

val zeros.Unfreeze = Cons 0 zeros

val (nats n).Unfreeze = Cons n (nats (n+1))

