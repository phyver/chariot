:set continue_on_error true
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

data bad_empty('a) where

codata bad_unit('a) where

data bad_empty where

codata bad_unit where

val i {} = ???
:show i

val j {} = ???
  | j {} = !!!
