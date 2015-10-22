(**********************************************************************
 *** tests with nested mu nu / nu mu / nu nu
 *********************************************************************)

:set verbose 1

--------------
-- basic types
data nat where
    | Zero : nat
    | Succ : nat -> nat

data plus('a,'b) where
    | Cons0 : 'a -> plus('a,'b)
    | Cons1 : 'b -> plus('a,'b)

codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)

-- X  |-->  nu Y . (X + Y)
codata nuY('x) where
    | Nu : nuY('x) -> plus('x,nuY('x))

-- X  |-->  mu Y . (X + Y)
data muY('x) where
    | Mu : plus('x,muY('x)) -> muY('x)


------------------------
-- mu X . mu Y . (X + Y)
-- this type is empty
data list1 where
    | C1 : muY(list1) -> list1

------------------------
-- nu X . mu Y . (X + Y)
-- infinite streams, with only finitely many consecutive 1s
codata stream2 where
    | D2 : stream2 -> muY(stream2)

------------------------
-- mu X . nu Y . (X + Y)
-- infinite streams, infinite number of 1s at the end (constructor Cons1)
data stream3 where
    | C3 : nuY(stream3) -> stream3

------------------------
-- nu x . nu y . (x + y)
-- infinite streams of 0 / 1 (constructors Cons0 / Cons1)
codata stream4 where
    | D4 : stream4 -> nuY(stream4)


-------------------------------------------------------
-- converting the different kinds of streams to "usual"
-- streams of natural numbers
val
    convert2 : stream2 -> stream(nat)
  | convert2 s = convert2_aux s.D2
and
  | (convert2_aux (Mu (Cons0 s))).Head = 0
  | (convert2_aux (Mu (Cons0 s))).Tail = convert2 s
  | (convert2_aux (Mu (Cons1 s))).Head = 1
  | (convert2_aux (Mu (Cons1 s))).Tail = convert2_aux s


val
    convert3 : stream3 -> stream(nat)
  | convert3 (C3 s) = convert3_aux s.Nu        -- s:nuY(stream3)  s.Nu:plus(stream3, nuY(stream3))
and
   convert3_aux : plus(stream3, nuY(stream3)) -> stream(nat)
  | (convert3_aux (Cons0 s)).Head = 0
  | (convert3_aux (Cons0 s)).Tail = convert3 s     -- s:stream3
  | (convert3_aux (Cons1 t)).Head = 1
  | (convert3_aux (Cons1 s)).Tail = convert3_aux (s.Nu)       -- s:nuY(stream3)


val convert4 : stream4 -> stream(nat)
  | convert4 s = convert4_aux s.D4.Nu
and
    convert4_aux : plus(stream4,nuY(stream4)) -> stream(nat)
  | (convert4_aux (Cons0 s)).Head = 0
  | (convert4_aux (Cons0 s)).Tail = convert4 s
  | (convert4_aux (Cons1 s)).Head = 1
  | (convert4_aux (Cons1 s)).Tail = convert4_aux s.Nu


-------------------------------------------------------
-- converting between the different kinds of streams

-- from stream2 to stream4
val stream2_to_4 : stream2 -> stream4
  | stream2_to_4 s = stream2_to_4_aux s.D2
and stream2_to_4_aux : muY(stream2) -> stream4
  | (stream2_to_4_aux (Mu (Cons0 s))).D4.Nu = Cons0 (stream2_to_4 s)
  | (stream2_to_4_aux (Mu (Cons1 s))).D4.Nu = Cons1 (stream2_to_4_aux s).D4


-- from stream3 to stream4
val stream3_to_4 : stream3 -> stream4
  | stream3_to_4 (C3 s) = stream3_to_4_aux s.Nu
and stream3_to_4_aux : plus(stream3,nuY(stream3)) -> stream4
  | (stream3_to_4_aux (Cons0 s)).D4.Nu = Cons0 (stream3_to_4 s)
  | (stream3_to_4_aux (Cons1 s)).D4.Nu = Cons1 (map_aux s)
and (map_aux s).Nu = map_aux2 s.Nu
and map_aux2 (Cons0 a) = Cons0 (stream3_to_4 a)
  | map_aux2 (Cons1 s) = Cons1 (map_aux s)

-- from stream3 to stream2, replacing 1s by 0s
val stream3_to_2_op : stream3 -> stream2
  | (stream3_to_2_op (C3 s)).D2 = stream3_to_2_op_aux s.Nu
and
    stream3_to_2_op_aux : plus(stream3,nuY(stream3)) -> muY(stream2)
  | stream3_to_2_op_aux (Cons0 s) = Mu (Cons1 (aux1 s))--:muY(stream2)     s:stream3
  | stream3_to_2_op_aux (Cons1 s) = Mu (Cons0 (aux2 s))--:stream2          s:nuY(stream3)
and aux1 : stream3 -> muY(stream2)
  | aux1 (C3 s) = stream3_to_2_op_aux s.Nu
and aux2 : nuY(stream3) -> stream2
  | (aux2 s).D2 = stream3_to_2_op_aux s.Nu


-------------------------------------------------------
-- constructing streams

-- only 0s
val zeros2 : stream2
  | zeros2.D2 = Mu (Cons0 zeros2)


-- construct 1110 1110 1110 1110 ... where each block contains n 1s
val
    ones_n2_aux : nat -> nat -> stream2
  | (ones_n2_aux 0 n).D2 = Mu (Cons0 (ones_n2_aux n n))
  | (ones_n2_aux (k+1) n).D2 = Mu (Cons1 (ones_n2_aux k n).D2)
val ones_n2 : nat -> stream2
  | ones_n2 n = ones_n2_aux n n


-- construct 01...1 01...1 01...1 ... where the i-th block of 1s contains (f i) 1s
val
    ones_f2_aux : (nat->nat) -> nat -> nat -> stream2
  | (ones_f2_aux f 0 i).D2 = Mu (Cons0 (ones_f2_aux f (f i) (i+1)))
  | (ones_f2_aux f (k+1) i).D2 = Mu (Cons1 (ones_f2_aux f k i).D2)
val ones_f2 : (nat -> nat) -> stream2
  | ones_f2 f = ones_f2_aux f 0 0

-- only 1s
val ones3_aux : nuY(stream3)
  | ones3_aux.Nu = Cons1 ones3_aux
val ones3 : stream3
  | ones3 = C3 ones3_aux

-- some 0s, then only 1s
val n_zeros_ones3 : nat -> stream3
  | n_zeros_ones3 0 = ones3
  | n_zeros_ones3 (n+1) = C3 (n_zeros_ones3_aux n)
and (n_zeros_ones3_aux n).Nu = Cons0 (n_zeros_ones3 n)


-- start like a given stream2 for some time, then only ones
val get_n_ones3 : nat -> stream2 -> stream3
  | get_n_ones3 n s = C3 (get_n_ones3_aux n s.D2)
and
    get_n_ones3_aux : nat -> muY(stream2) -> nuY(stream3)
  | get_n_ones3_aux 0 s = ones3_aux
  | (get_n_ones3_aux (n+1) (Mu (Cons0 s))).Nu = Cons0 (get_n_ones3 n s)
  | (get_n_ones3_aux (n+1) (Mu (Cons1 s))).Nu = Cons1 (get_n_ones3_aux n s)

-- get the length of blocks of 1s
val
    map_length1 : stream2 -> stream(nat)
  | map_length1 s = map_length1_aux s.D2 0
and
    map_length1_aux : muY(stream2) -> nat -> stream(nat)
  | (map_length1_aux (Mu (Cons0 s)) n).Head = n
  | (map_length1_aux (Mu (Cons0 s)) n).Tail = map_length1 s
  | (map_length1_aux (Mu (Cons1 s)) n) = map_length1_aux s (n+1)


-- tests

-- only zeros
val test1 = convert2 zeros2
:unfold test1, 3

-- blocs of 3 1s,
val test2 = convert2 (ones_n2 3)
:unfold test2, 9

-- blocs of 3 1s, other version
val k3 n = 3
val test3 = convert2 (ones_f2 k3)
:unfold test3, 9

-- blocs of 1s of increasing length
val id n = n
val test4 = convert2 (ones_f2 id)
:unfold test4, 16

-- only 1s
val test5 = convert3 (ones3)
:unfold test5, 6

-- 5 0s,then only 1s
val test6 = convert3 (n_zeros_ones3 5)
:unfold test6, 9

-- increasing blocks of 1s, then only 1s
val test7 = convert3 (get_n_ones3 11 (ones_f2 id))
:unfold test7, 20

-- length of the blocs of ones
val test8 = map_length1 (ones_n2 3)
:unfold test8, 10

val test9 =map_length1 (ones_f2 k3)
:unfold test9, 10

val test10 = map_length1 (ones_f2 id)
:unfold test10, 10

-- blocs of 1s of increasing length, after conversion to stream4
val test12 = convert4 (stream2_to_4 (ones_f2 id))
-- :unfold test12, 16

-- increasing blocks of 1s, then only 1s, after conversion to stream4
val test13 = convert4 (stream3_to_4 (get_n_ones3 11 (ones_f2 id)))
:unfold test13, 20

-- five 1s, then only 0s
val test14 = convert2 (stream3_to_2_op (n_zeros_ones3 5))
:unfold test14, 12


(*
-- other, malfunctioning definitions
val
    cons3_aux : nat -> nuY(stream3) -> nuY(stream3)
  | (cons3_aux 0 s).Nu = Cons0 (C3 s)
  | (cons3_aux 1 s).Nu = Cons1 s
  | (cons3_aux n s).Nu = !!!
 val cons3 : nat -> stream3 -> stream3
   | cons3 k (C3 s) = C3 (cons3_aux k s)

-- doesn't terminate
val ones3_bad : stream3
  | ones3_bad = cons3 1 ones3_bad


val map_nuY : ('a -> 'b) -> nuY('a) -> nuY('b)
  | (map_nuY f s).Nu = map_nuY_aux f s.Nu
and
    map_nuY_aux : ('a -> 'b) -> plus('a,nuY('a)) -> plus('b,nuY('b))
  | map_nuY_aux f (Cons0 a) = Cons0 (f a)
  | map_nuY_aux f (Cons1 s) = Cons1 (map_nuY f s)

-- the next version doesn't pass the SCP because of recursive call via map_nuY
val stream3_to_4_bad: stream3 -> stream4
  | stream3_to_4_bad (C3 s) = stream3_to_4_bad_aux s.Nu
and stream3_to_4_bad_aux : plus(stream3,nuY(stream3)) -> stream4
  | (stream3_to_4_bad_aux (Cons0 s)).D4.Nu = Cons0 (stream3_to_4_bad s)
  | (stream3_to_4_bad_aux (Cons1 s)).D4.Nu = Cons1 (map_nuY stream3_to_4_bad s)
*)

