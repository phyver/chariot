data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val test2 f [] x = []
  | test2 f x [] = []
  | test2 f (x::xs) (y::ys) = test2 f (y::xs) (x::ys)
