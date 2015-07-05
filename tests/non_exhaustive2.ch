:set dont_show_priorities

data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

:set dont_check_completeness

val last [x] = x
  | last (x::xs) = last xs

:show last

:unset dont_check_completeness

val last2 [x] = x
  | last2 (x::xs) = last2 xs


