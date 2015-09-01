data bool where True | False : bool

val f True = False
  | f False = f True

val g True = False
  | g x = g True

:set expand_clauses true
val h True = False
  | h x = h True


