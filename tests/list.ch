
data
  list('x) where Nil : list('x)
               | Cons : 'x -> list('x) -> list('x)

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

val length : list('x) -> nat
    | length Nil = Zero
    | length (Cons x xs) = Succ (length xs)

val map f [] = []
  | map f x::xs = (f x)::(map f xs)

val decr 0 = []
  | decr (n+1) = n::(decr n)

val rev_append l [] = l
  | rev_append l (x::xs) = rev_append (x::l) xs

val rev l = rev_append [] l

:set dont_show_lists
:show functions

:unset dont_show_lists
:show functions


