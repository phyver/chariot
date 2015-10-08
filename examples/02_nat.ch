data nat where Zero : nat | Succ : nat -> nat

val add : nat -> nat -> nat
    | add m 0 = m
    | add m (n+1) = Succ (add m n)

val sub : nat -> nat -> nat
  | sub m 0 = m
  | sub 0 _ = 0
  | sub (m+1) (n+1) = sub m n

val mult : nat -> nat -> nat
    | mult m 0 = 0
    | mult m (n+1) = m + (mult m n)

val pow : nat -> nat -> nat
    | pow m 0 = 1
    | pow m (n+1) = mult m (pow m n)

val fib 0 = 0
  | fib 1 = 1
  | fib (n+2) = add (fib n) (fib (n+1))

val ack 0 n = n+1
  | ack (m+1) 0 = ack m 1
  | ack (m+1) (n+1) = ack m (ack (m+1) n)


