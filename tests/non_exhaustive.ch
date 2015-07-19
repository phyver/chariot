:set continue_on_error true
:set show_priorities false

data nat where Zero : nat | Succ : nat -> nat

(* INCOMPLETE *)
val f 0 = ???
  | f (n+2) = ???


data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

:set check_completeness false

val last [x] = x
  | last (x::xs) = last xs

:show last

:set check_completeness true

val last2 [x] = x
  | last2 (x::xs) = last2 xs


