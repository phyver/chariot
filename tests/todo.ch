:set allow_structs true

codata stru where
    | Tail : stru -> stru

data c_stru where
    | C : stru -> c_stru

codata stru_d where
    | D : stru_d -> stru


:set show_bad_loops true
:set incremental_SCT false
:set depth 4
:set bound 4
:set verbose 1

-- :set squash_priorities true
-- :set show_all_steps true

-- TODO: the SCT doesn't see that this version terminates without squash_priorities set to true
-- should it?
-- f seems to terminate
val f : c_stru -> stru_d
  | f (C { Tail = s }) = D # { Tail = (f $ C s).D }

-- g doesn't terminate
val g : c_stru -> stru_d
  | g (C s) = D # (g (C s)).D

val s : stru
  | s = { Tail = s }

val x : c_stru
  | x = C s

-- :unfold f x , 1          -- terminates
-- :unfold g x , 1          -- loops
