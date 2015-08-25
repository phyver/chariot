:set verbose 1
:set continue_on_error true
:set show_priorities false

data nat where Zero : nat | Succ : nat -> nat

(* INCOMPLETE *)
val f 0 = ???
  | f (n+2) = ???


data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

:set allow_incomplete_defs true

val last [x] = x
  | last (x::xs) = last xs

:set allow_incomplete_defs false

val last2 [x] = x
  | last2 (x::xs) = last2 xs


val merge f [] ys = ys
  | merge f xs [] = xs
  | merge f (x::xs) (y::ys) = (f x y)::(merge f xs ys)

val test1 [a] = 1
  | test1 [a;b;c] = 2
  | test1 (a::b::c::d::e::l) = 3



