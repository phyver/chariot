-- :set allow_structs true

codata t where D : t -> t

val f a b c d = D# a b c d

val g a b c d = D# a $ b $ c d

val h a = D # D # D # a

:show functions
