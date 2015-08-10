data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

-- shouldn't terminate
val test1 f [] x = []
  | test1 f x [] = []
  | test1 f (x::xs) (y::ys) = test1 f (y::xs) (x::ys)

-- should terminate
val test1 f [] x = []
  | test1 f x [] = []
  | test1 f (x::xs) (y::ys) = test1 f ??? (x::ys)

-- should terminate
val test1 f [] x = []
  | test1 f x [] = []
  | test1 f (x::xs) (y::ys) = test1 f (x::xs) ???

-- shouldn't terminate
val test1 f [] x = []
  | test1 f x [] = []
  | test1 f (x::xs) (y::ys) = test1 ??? (y::xs) (x::ys)

