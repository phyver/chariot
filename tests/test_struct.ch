:set show_tuples false
:set verbose 1
:set allow_structs true

data prod_2('a,'b) where Tuple_2 : 'a -> 'b -> prod_2('a,'b)

codata struct_2('a,'b) where Fst : struct_2('a,'b) -> 'a | Snd : struct_2('a,'b) -> 'b

val f : struct_2('a,'b) -> prod_2('a,'b)
  | f p = Tuple_2 p.Fst p.Snd

val g : struct_2('a,'b) -> prod_2('a,'b)
  | g { Fst = x ; Snd = y } = Tuple_2 x y

val h { Fst = x ; Snd = { Fst = y ; Snd = z } } = Tuple_2 (Tuple_2 x y) z

:show functions

