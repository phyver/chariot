:set incremental_SCP false
:set show_all_steps true
:set show_bad_loops true
:set depth 3

data nat where Zero : nat | Succ : nat -> nat

data list('x) where Nil : list('x) | Cons : 'x -> list('x) -> list('x)

val length [] = 0
  | length x::xs = (length xs) + 1
