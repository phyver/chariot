:set incremental_SCP false
:set depth 3
:set show_lists false
-- :set show_all_steps true

data nat where
    | Zero : nat
    | Succ : nat -> nat

val add m (n+1) = (add n m) + 1
  | add m 0 = m

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val sum [] = 0
  | sum [n] = n
  | sum m::n::l = sum ((m+n)::l)

-- exemple 2
codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

val sums { Head = [] ; Tail = s }      = { Head = 0 ; Tail = sums s }
  | sums { Head = [n] ; Tail = s }     = { Head = n ; Tail = sums s }
  | sums { Head = n::m::l ; Tail = s } = sums { Head = (add n m)::l ; Tail = s }
