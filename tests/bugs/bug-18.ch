:set verbose 1
-- :set allow_structs true

data nat where Zero : nat | Succ : nat -> nat

codata stream('n) where
    | Head : stream('n) -> 'n
    | Tail : stream('n) -> stream('n)

codata prod('a,'b) where
    | Fst : prod('a,'b) -> 'a
    | Snd : prod('a,'b) -> 'b

-- :set squash_priorities true

-- TODO: the SCT didn't see that this version terminates without squash_priorities set to true
-- The problem is that prod(...) has priority 4 and stream(nat) has priority 2
-- In the following, the greatest move appearing infinitely often is Tail, with priority 2.
-- The test should give TRUE
-- However, the move Snd, that comes and goes (=> weight 0) has priority 4, and
-- while adding them, I only keep <0>4 and the test concludes FALSE
val f : stream(nat) → prod(nat,stream(nat))
  | f { Head = n ; Tail = s } = { Fst = n ; Snd = { Head = n ; Tail = (f s).Snd } }



-- val nats n = { Head = n ; Tail = nats (n+1) }

-- val test = f $ nats 3

