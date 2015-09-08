data nat where Zero : nat | Succ : nat -> nat

val add : nat -> nat -> nat
    | add n 0 = n
    | add n (m+1) = Succ (add n m)

val mult : nat -> nat -> nat
    | mult n 0 = 0
    | mult n (m+1) = n + (mult n m)

val pow : nat -> nat -> nat
    | pow n 0 = 1
    | pow n (m+1) = mult n (pow n m)

val fib 0 = 0
  | fib 1 = 1
  | fib (n+2) = add (fib n) (fib (n+1))

val ack 0 n = n+1
  | ack (m+1) 0 = ack m 1
  | ack (m+1) (n+1) = ack m (ack (m+1) n)


