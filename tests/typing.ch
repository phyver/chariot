:set show_priorities false


data nat where Zero : nat | Succ : nat -> nat

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val map f [] = []
  | map f (x::xs) = (f x)::(map f xs)

val map1 : ('a -> 'b) -> list('a) -> list('b)
  | map1 f [] = []
  | map1 f (x::xs) = (f x)::(map1 f xs)

val map2 : (nat -> nat) -> list(nat) -> list(nat)
  | map2 f [] = []
  | map2 f (x::xs) = (f x)::(map2 f xs)

val map3 : ('a -> nat) -> list('a) -> list(nat)
  | map3 f [] = []
  | map3 f (x::xs) = (f x)::(map3 f xs)

val map4 : (nat -> list('a)) -> list(nat) -> list(list('a))
  | map4 f [] = []
  | map4 f (x::xs) = (f x)::(map4 f xs)

:show functions

val map5 : ('a -> 'b) -> list('b) -> list('a)
  | map5 f [] = []
  | map5 f (x::xs) = (f x)::(map5 f xs)
