data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

-- BUG: cannot unify: loop
val test x = []
  | test [] = []

:show test

-- it used to provoke a "unify loop" error because of interferences between
-- the type variables used for the first / second clause
-- the fix was to not reset de the generator for type variable for each
-- clause, but only once for each bunch of definitions
