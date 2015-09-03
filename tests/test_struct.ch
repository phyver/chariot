:set show_tuples false
:set verbose 1
:set allow_structs true

data nat where Zero : nat | Succ : nat -> nat

data prod_2('a,'b) where Tuple_2 : 'a -> 'b -> prod_2('a,'b)

codata struct_2('a,'b) where Fst : struct_2('a,'b) -> 'a | Snd : struct_2('a,'b) -> 'b

val s01 = { Fst =  0 ; Snd = 1}
val s012 = { Fst =  0 ; Snd = { Fst = 1 ; Snd = 2 } }


val f : struct_2('a,'b) -> prod_2('a,'b)
  | f p = Tuple_2 p.Fst p.Snd

val g : struct_2('a,'b) -> prod_2('a,'b)
  | g { Fst = x ; Snd = y } = Tuple_2 x y

val h { Fst = x ; Snd = { Fst = y ; Snd = z } } = Tuple_2 (Tuple_2 x y) z

val s { Fst = x ; Snd = { Fst = y ; Snd = z } } = { Fst = { Fst = x ; Snd = y } ; Snd = z }


codata stream('x) where Head : stream('x) -> 'x | Tail : stream('x) -> stream('x)

val map f { Head = x ; Tail = s } = { Head = f x ; Tail = map f s }


:show functions

