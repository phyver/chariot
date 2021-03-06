:set show_priorities false

(* tests to check that types are parsed correctly *)

data nat where Zero : nat | Succ : nat -> nat

data nat2 where | Zero2 : nat2 | Succ2 : nat2 -> nat2

data nat3 where
      Zero3 : nat3
    | Succ3 : nat3 -> nat3

data nat4 where
    | Zero4 : nat4
    | Succ4 : nat4 -> nat4

data nat5 where
    | Zero5 : nat5
    | Succ5 : nat5 → nat5

codata stream('x) where Head : stream('x) → 'x | Tail : stream('x) → stream('x)

codata stream2('a) where
    | Head2 : stream2('a) -> 'a
    | Tail2 : stream2('a) -> stream('a)

data
    rtree('n) where
        | Node : 'n -> sons('n) -> rtree('n)
 and
    sons('n) where
        | Nil : sons('n)
        | Cons : rtree('n) -> sons('n) -> sons('n)


:show types
