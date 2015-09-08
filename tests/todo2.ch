:set show_nats false
:set show_lists false

data nat where Zero : nat | Succ : nat -> nat

val add : nat -> nat -> nat
    | add n 0 = n
    | add n (m+1) = (add n m) + 1

val mult : nat -> nat -> nat
    | mult n 0 = 0
    | mult n (m+1) = n + (mult n m)

val pow : nat -> nat -> nat
    | pow n 0 = 1
    | pow n (m+1) = mult n (pow n m)


codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

data list('x) where Nil : list('x)
                  | Cons : 'x -> list('x) -> list('x)

-- val test { Head = [] ; Tail = s } = { Head = 0 ; Tail = test s }
--   | test { Head = [n] ; Tail = s } = { Head = n ; Tail = test s }
--   | test { Head = a::b::l ; Tail = s } = test { Head = (add a b)::l ; Tail = s }


-- this doesn't pass the SCT, but it should!!!
-- the problem is that the call to test1_aux2 hides important information
val test1 s = test1_aux s.Head s.Tail
and
    (test1_aux [] s).Head = 0
  | (test1_aux [] s).Tail = test1 s
  | (test1_aux [n] s).Head = n
  | (test1_aux [n] s).Tail = test1 s
  | test1_aux (a::b::l) s = test1 (test1_aux2 (add a b) l s)
and
    (test1_aux2 c l s).Head = c::l
  | (test1_aux2 c l s).Tail = s
