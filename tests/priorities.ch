data nat where Zero : nat | Succ : nat -> nat

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val f [[[[0]]]] = 0
  | f x = 0

val g1 x = []


val g2 : nat -> list(list(list(nat)))
  | g2 x = []


:set dont_show_lists
:set dont_show_nats

:show functions
