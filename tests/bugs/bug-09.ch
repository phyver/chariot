codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

:set show_initial_graph true
-- this shouldn't be seen as terminating
val f x = f x.Tail

