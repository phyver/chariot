data nat where Zero : nat | Succ : nat -> nat

data unit where Tuple_0 : unit

data prod_2('a,'b) where Tuple_2 : 'a -> 'b -> prod_2('a,'b)

val fst (x,y) = x

val snd (x,y) = y

val pair = (0,0)


:set show_lists false

data list('x) where
    | Nil : unit -> list('x)
    | Cons : 'x * list('x) -> list('x)

val onetwothree = Cons (1 , Cons (2 , Cons (3,Nil ())))

val pairs = (1,(2,(3,4)))

:show functions


data prod_3('a,'b,'c) where Tuple_3 : 'a -> 'b -> 'c -> prod_3('a,'b,'c)

val test = (1,2,3)

:show test

:set continue_on_error true

val bad = (1,2,3,4)


:set show_tuples false

:show functions
