(* coinductive type: streams *)
codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)

data process_aux('a,'b,'x) where
    | Output : 'b -> 'x -> process_aux('a,'b,'x)
    | Input :  ('a -> process_aux('a,'b,'x)) -> process_aux('a,'b,'x)

codata process('a,'b) where
    | D : process('a,'b) -> process_aux('a,'b,process('a,'b))

-- TODO bug with structures...
-- val eating : process('a,'b) -> stream('a) -> stream('b)
--   | eating (D # Output b p) s = { Head = b ; Tail = eating p s}
--   | eating (D # Input phi) { Head = a ; Tail = s } = eating (D # phi a) s


-- that version works...
-- val eating : process('a,'b) -> stream('a) -> stream('b)
--   | eating p s = eating1 p.D s
-- and (eating1 (Output b p) s) = { Head = b ; Tail = eating p s }
--   | eating1 (Input phi) { Head = a ; Tail = s } = eating1 (phi a) s

-- -- that version doesn't pass the termination checker because the auxiliary
-- -- function introduced to deal with structures in argument position on the
-- -- right hides the relevant information...
:set incremental_SCT false
:set show_bad_loops true
:set show_all_steps true
val eating : process('a,'b) -> stream('a) -> stream('b)
  -- | eating (D # Output b p) { Head = a ; Tail = s } = { Head = b ; Tail = eating p  { Head = a ; Tail = s }}
  | eating (D # Input phi) { Head = a ; Tail = s } = eating (D # phi a) s

