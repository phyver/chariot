data nat where Zero : nat | Succ : nat -> nat

val f (Succ _) = 0
  | f 0 = 0
:show f
