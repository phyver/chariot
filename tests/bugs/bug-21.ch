codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

val f { Head = x ; Tail = { Head = y ; Tail = { Head = z ; Tail = zs }}} = z

:set verbose 2
:show f
