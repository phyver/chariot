:set unary_constants true
:set continue_on_error true

codata unit where

data nat where Z : unit -> nat
             | S : nat -> nat

codata prod('x,'y) where Fst : prod('x,'y) -> 'x
                       | Snd : prod('x,'y) -> 'y

data list('x) where
    | Nil : unit -> list('x)
    | Cons : prod('x,list('x)) -> list('x)

data oops where Zero : oops
              | Succ : oops -> oops

val map_list f (Nil {}) = Nil {}
  | map_list f (Cons { Fst = x ; Snd = xs }) = Cons { Fst = f x ; Snd = map_list f xs }
:show map_list
