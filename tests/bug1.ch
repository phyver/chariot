data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

-- BUG: cannot unify: loop
val test1 x = []
  | test1 [] = []
