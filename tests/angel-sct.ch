data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

-- shouldn't terminate
val test1 f [] x = []
  | test1 f x [] = []
  | test1 f (x::xs) (y::ys) = test1 f (y::xs) (x::ys)

-- should terminate
val test2 f [] x = []
  | test2 f x [] = []
  | test2 f (x::xs) (y::ys) = test2 f ??? (x::ys)

-- should terminate
val test3 f [] x = []
  | test3 f x [] = []
  | test3 f (x::xs) (y::ys) = test3 f (x::xs) ???

-- shouldn't terminate
val test4 f [] x = []
  | test4 f x [] = []
  | test4 f (x::xs) (y::ys) = test4 ??? (y::xs) (x::ys)

