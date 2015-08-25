:set show_lists false


data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

-- BUG: this was seen as incomplete!
val test x [] = []
  | test [] y = []
  | test (u::xs) (v::ys) = test (u::xs) (v::ys)
