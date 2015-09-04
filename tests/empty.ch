:set verbose 2

data empty where


codata unit where


val f : 'a -> 'a -> 'b -> empty -> 'b

val g : 'a -> 'a -> 'b -> empty

val h : 'a -> 'a -> 'b -> unit

:show functions

:show f

:show g

:show h
