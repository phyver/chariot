
data nat where Zero : nat | Succ : nat -> nat

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val map f [] = []
  | map f (x::xs) = (f x)::(map f xs)

val map1 : ('a -> 'b) -> list('a) -> list('b)
  | map1 f [] = []
  | map1 f (x::xs) = (f x)::(map1 f xs)

val map2 : (int -> int) -> list(int) -> list(int)
  | map2 f [] = []
  | map2 f (x::xs) = (f x)::(map2 f xs)

val map3 : ('a -> int) -> list('a) -> list(int)
  | map3 f [] = []
  | map3 f (x::xs) = (f x)::(map3 f xs)

val map4 : (int -> list('a)) -> list(int) -> list(list('a))
  | map4 f [] = []
  | map4 f (x::xs) = (f x)::(map4 f xs)

:show functions

val map5 : ('a -> 'b) -> list('b) -> list('a)
  | map5 f [] = []
  | map5 f (x::xs) = (f x)::(map5 f xs)
