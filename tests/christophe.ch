:set verbose 1

data unit where Tuple_0 : unit

data nat where
    | Zero : nat
    | Succ : nat -> nat

data plus('a,'b) where
    | Cons0 : 'a -> plus('a,'b)
    | Cons1 : 'b -> plus('a,'b)

codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)


-----------------
-- nu X . (X + X)
codata stream1 where
    | Unfold1 : stream1 -> plus(unit,unit)

--------------------------
-- X  |-->  nu Y . (X + Y)
codata nuY('x) where
    | DNuY : nuY('x) -> plus('x,nuY('x))

--------------------------
-- X  |-->  mu Y . (X + Y)
data muY('x) where
    | MuY0 : 'x -> muY('x)
    | MuY1 : muY('x) -> muY('x)

------------------------
-- mu X . mu Y . (X + Y)
data list1 where
    | Cons : muY(list1) -> list1
-- should be empty

------------------------
-- nu X . mu Y . (X + Y)
-- infinite streams, only finitely many consecutive 1s
codata stream2 where
    | Unfold2 : stream2 -> muY(stream2)

val
    convert2 : stream2 -> stream(nat)
  | convert2 s = convert2_aux s.Unfold2
and
  | (convert2_aux (MuY0 s)).Head = 0
  | (convert2_aux (MuY0 s)).Tail = convert2 s
  | (convert2_aux (MuY1 s)).Head = 1
  | (convert2_aux (MuY1 s)).Tail = convert2_aux s


-- construct 1110 1110 1110 1110 ... where each block contains n 1s
val zeros2 : stream2
  | zeros2.Unfold2 = MuY0 zeros2

val
    ones_n2_aux : nat -> nat -> stream2
  | (ones_n2_aux 0 n).Unfold2 = MuY0 (ones_n2_aux n n)
  | (ones_n2_aux (k+1) n).Unfold2 = MuY1 (ones_n2_aux k n).Unfold2
val ones_n2 : nat -> stream2
  | ones_n2 n = ones_n2_aux n n


-- construct 1...10 1...10 1...10 ... where the i-th block of 1s contains (f i) 1s
val
    ones_f2_aux : (nat->nat) -> nat -> nat -> stream2
  | (ones_f2_aux f 0 i).Unfold2 = MuY0 (ones_f2_aux f (f i) (i+1))
  | (ones_f2_aux f (k+1) i).Unfold2 = MuY1 (ones_f2_aux f k i).Unfold2

val
    map_length1 : stream2 -> stream(nat)
  | map_length1 s = map_length1_aux s.Unfold2 0
and
    map_length1_aux : muY(stream2) -> nat -> stream(nat)
  | (map_length1_aux (MuY0 s) n).Head = n
  | (map_length1_aux (MuY0 s) n).Tail = map_length1 s
  | (map_length1_aux (MuY1 s) n) = map_length1_aux s (n+1)

------------------------
-- mu X . nu Y . (X + Y)
-- infinite streams, infinite number of 1s at the end
data stream3 where
    | Cons3 : nuY(stream3) -> stream3

val
    convert3 : stream3 -> stream(nat)
  | convert3 (Cons3 s) = convert3_aux s.DNuY                    -- s:nuY(stream3)  s.DNuY:plus(stream3, nuY(stream3))
and
   convert3_aux : plus(stream3, nuY(stream3)) -> stream(nat)
  | (convert3_aux (Cons0 s)).Head = 0
  | (convert3_aux (Cons0 s)).Tail = convert3 s                  -- s:stream3
  | (convert3_aux (Cons1 t)).Head = 1
  | (convert3_aux (Cons1 s)).Tail = convert3_aux (s.DNuY)       -- s:nuY(stream3)

val
    cons3_aux : nat -> nuY(stream3) -> nuY(stream3)
  | (cons3_aux 0 s).DNuY = Cons0 (Cons3 s)
  | (cons3_aux 1 s).DNuY = Cons1 s
  | (cons3_aux n s).DNuY = !!!
 val cons3 : nat -> stream3 -> stream3
   | cons3 k (Cons3 s) = Cons3 (cons3_aux k s)

-- -- doesn't terminate
-- val ones3_bad : stream3
--   | ones3_bad = cons3 1 ones3_bad

val ones3_aux : nuY(stream3)
  | ones3_aux.DNuY = Cons1 ones3_aux
val ones3 : stream3
  | ones3 = Cons3 ones3_aux

val n_zeros_ones3 : nat -> stream3
  | n_zeros_ones3 0 = ones3
  | n_zeros_ones3 (n+1) = Cons3 (n_zeros_ones3_aux n)
and (n_zeros_ones3_aux n).DNuY = Cons0 (n_zeros_ones3 n)

val get_n_ones3 : nat -> stream2 -> stream3
  | get_n_ones3 n s = Cons3 (get_n_ones3_aux n s.Unfold2)
and
    get_n_ones3_aux : nat -> muY(stream2) -> nuY(stream3)
  | get_n_ones3_aux 0 s = ones3_aux
  | (get_n_ones3_aux (n+1) (MuY0 s)).DNuY = Cons0 (get_n_ones3 n s)
  | (get_n_ones3_aux (n+1) (MuY1 s)).DNuY = Cons1 (get_n_ones3_aux n s)


-- convert a stream3 into a stream2 by inverting 0 and 1
val stream3_to_2_op : stream3 -> stream2
  | (stream3_to_2_op (Cons3 s)).Unfold2 = stream3_to_2_op_aux s.DNuY
and
    stream3_to_2_op_aux : plus(stream3,nuY(stream3)) -> muY(stream2)
  | stream3_to_2_op_aux (Cons0 s) = MuY1 (aux1 s)--:muY(stream2)     s:stream3
  | stream3_to_2_op_aux (Cons1 s) = MuY0 (aux2 s)--:stream2          s:nuY(stream3)
and aux1 : stream3 -> muY(stream2)
  | aux1 (Cons3 s) = stream3_to_2_op_aux s.DNuY
and aux2 : nuY(stream3) -> stream2
  | (aux2 s).Unfold2 = stream3_to_2_op_aux s.DNuY






------------------------
-- nu x . nu y . (x + y)
-- infinite streams of 0 / 1
codata stream4 where
    | Unfold4 : stream4 -> nuY(stream4)

val convert4 : stream4 -> stream(nat)
  | convert4 s = convert4_aux s.Unfold4.DNuY
and
    convert4_aux : plus(stream4,nuY(stream4)) -> stream(nat)
  | (convert4_aux (Cons0 s)).Head = 0
  | (convert4_aux (Cons0 s)).Tail = convert4 s
  | (convert4_aux (Cons1 s)).Head = 1
  | (convert4_aux (Cons1 s)).Tail = convert4_aux s.DNuY

val stream2_to_4 : stream2 -> stream4
  | stream2_to_4 s = stream2_to_4_aux s.Unfold2
and stream2_to_4_aux : muY(stream2) -> stream4
  | (stream2_to_4_aux (MuY0 s)).Unfold4.DNuY = Cons0 (stream2_to_4 s)
  | (stream2_to_4_aux (MuY1 s)).Unfold4.DNuY = Cons1 (stream2_to_4_aux s).Unfold4


val map_nuY : ('a -> 'b) -> nuY('a) -> nuY('b)
  | (map_nuY f s).DNuY = map_nuY_aux f s.DNuY
and
    map_nuY_aux : ('a -> 'b) -> plus('a,nuY('a)) -> plus('b,nuY('b))
  | map_nuY_aux f (Cons0 a) = Cons0 (f a)
  | map_nuY_aux f (Cons1 s) = Cons1 (map_nuY f s)

-- -- the next version doesn't pass the SCT because of recursive call via map_nuY
-- val stream3_to_4 : stream3 -> stream4
--   | stream3_to_4 (Cons3 s) = stream3_to_4_aux s.DNuY
-- and stream3_to_4_aux : plus(stream3,nuY(stream3)) -> stream4
--   | (stream3_to_4_aux (Cons0 s)).Unfold4.DNuY = Cons0 (stream3_to_4 s)
--   | (stream3_to_4_aux (Cons1 s)).Unfold4.DNuY = Cons1 (map_nuY stream3_to_4 s)

val stream3_to_4 : stream3 -> stream4
  | stream3_to_4 (Cons3 s) = stream3_to_4_aux s.DNuY
and stream3_to_4_aux : plus(stream3,nuY(stream3)) -> stream4
  | (stream3_to_4_aux (Cons0 s)).Unfold4.DNuY = Cons0 (stream3_to_4 s)
  | (stream3_to_4_aux (Cons1 s)).Unfold4.DNuY = Cons1 (map_aux s)
and (map_aux s).DNuY = map_aux2 s.DNuY
and map_aux2 (Cons0 a) = Cons0 (stream3_to_4 a)
  | map_aux2 (Cons1 s) = Cons1 (map_aux s)

