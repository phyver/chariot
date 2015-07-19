val k x y = x

val s x y z = x z (y z)

val i = s k k

:show functions


(* AMEN combinators *)

val a i j f x = i f (j f x)

val m i j f = i (j f)

val e i j = j i

val n f x = x

:show functions

val one = e n n

val two = a one one

val three = a one two

val four = m two two

val nine = e three two


data nat where Zero : nat | Succ : nat -> nat

:reduce one Succ Zero

:reduce two Succ Zero

:reduce three Succ Zero

:reduce four Succ Zero

:reduce nine Succ Zero


