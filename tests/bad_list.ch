-- simple terminating infinite list using lazy product type

codata prod_2('a,'b) where
    Fst : prod_2('a,'b) -> 'a
  | Snd : prod_2('a,'b) -> 'b

data list('a) where
    Nil : list('a)
  | Cons : 'a * list('a) -> list('a)

data nat where Zero : nat | Succ : nat -> nat

val bad : nat -> nat * list(nat)
  | (bad n).Fst = n
  | (bad n).Snd = Cons (bad (Succ n))

val inf : list(nat)
  | inf = Cons (bad 0)

:show bad
