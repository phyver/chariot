:set continue_on_error true

data nat where Zero : nat | Succ : nat -> nat

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

(* OK *)
val
  | map_1 f [] = []
  | map_1 f (x::xs) = (f x)::(map_2 f xs)
and
  | map_2 f [] = []
  | map_2 f (x::xs) = (f x)::(map_1 f xs)

(* OK *)
val
    map1_1 : ('a -> 'b) -> list('a) -> list('b)
  | map1_1 f [] = []
  | map1_1 f (x::xs) = (f x)::(map1_2 f xs)
and
    map1_2 : ('a -> 'b) -> list('a) -> list('b)
  | map1_2 f [] = []
  | map1_2 f (x::xs) = (f x)::(map1_1 f xs)

(* OK *)
val
    map2_1 : (nat -> nat) -> list(nat) -> list(nat)
  | map2_1 f [] = []
  | map2_1 f (x::xs) = (f x)::(map2_2 f xs)
and
  | map2_2 f [] = []
  | map2_2 f (x::xs) = (f x)::(map2_1 f xs)

(* problem *)
val
    map3_1 : ('a -> 'b) -> list('a) -> list('b)
  | map3_1 f [] = []
  | map3_1 f (x::xs) = (f x)::(map3_2 f xs)
and
    map3_2 : (nat -> nat) -> list(nat) -> list(nat)
  | map3_2 f [] = []
  | map3_2 f (x::xs) = (f x)::(map3_1 f xs)

(* problem *)
val
    map4_1 : (nat -> nat) -> list(nat) -> list(nat)
  | map4_1 f [] = []
  | map4_1 f (x::xs) = (f x)::(map4_2 f xs)
and
    map4_2 : ('a -> 'b) -> list('a) -> list('b)
  | map4_2 f [] = []
  | map4_2 f (x::xs) = (f x)::(map4_1 f xs)

:show functions
