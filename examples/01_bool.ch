data bool where
    | True | False : bool

val not True = False
  | not False = True

val land True True = True
  | land _ _ = False

val lor False False = False
  | lor _ _ = True


