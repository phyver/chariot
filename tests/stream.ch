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


codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

val map : ('x -> 'y) -> stream('x) -> stream('y)
    | (map f s).Head = f (s.Head)
    | (map f s).Tail = map f s.Tail

val arith : nat -> nat -> stream(nat)
  | (arith n r).Head = n
  | (arith n r).Tail = arith (n+r) r

val get_nth : nat -> stream('a) -> 'a
  | get_nth Zero s = s.Head
  | get_nth (Succ n) s = get_nth n s.Tail

val double : nat -> nat | double n = mult n 2

:reduce map double (arith 3 3)

:reduce get_nth (mult 3 3) (map double (arith 3 3))


val (fib n m).Head = n
  | (fib n m).Tail = fib m (n+m)


:reduce get_nth (4+7) (map double (fib 0 1))

