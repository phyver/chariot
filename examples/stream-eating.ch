(* coinductive type: streams *)
codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)

data process_aux('a,'b,'x) where
    | Output : 'b -> 'x -> process_aux('a,'b,'x)
    | Input :  ('a -> process_aux('a,'b,'x)) -> process_aux('a,'b,'x)

codata process('a,'b) where
    | D : process('a,'b) -> process_aux('a,'b,process('a,'b))

val eating : process('a,'b) -> stream('a) -> stream('b)
  | eating (D # Output b p) s = { Head = b ; Tail = eating p s}
  | eating (D # Input phi) { Head = a ; Tail = s } = eating (D # phi a) s

