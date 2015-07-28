data nat where Zero : nat | Succ : nat -> nat

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val f [[[[0]]]] = 0
  | f x = 0

val g1 x = []


val g2 : nat -> list(list(list(nat)))
  | g2 x = []


:set show_lists false
:set show_nats false

:show functions

:set squash_priorities true
val f1 [[[[0]]]] = 0
  | f1 x = 0

:show f1
