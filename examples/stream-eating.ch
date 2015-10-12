-- Hancock stream processors

:set verbose 1

data nat where
    | Zero : nat
    | Succ : nat -> nat

val add : nat -> nat -> nat
    | add m 0 = m
    | add m (n+1) = (add m n) + 1


-- infinite lists
codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)

val arith n r = { Head = n ; Tail = arith (add n r) r }


-- auxiliary sum type for stream processors
data process_aux('a,'b,'x) where
    | Output : 'b -> 'x -> process_aux('a,'b,'x)
    | Input :  ('a -> process_aux('a,'b,'x)) -> process_aux('a,'b,'x)

-- type of stream processors
codata process('a,'b) where
    | D : process('a,'b) -> process_aux('a,'b,process('a,'b))



-- the "eating function", transforming a stream processor into a function on streams
val eating : process('a,'b) -> stream('a) -> stream('b)
  | eating (D # Output b p) s = { Head = b ; Tail = eating p s}
  | eating (D # Input phi) { Head = a ; Tail = s } = eating (D # phi a) s


-- the composition for stream processor
val compose : process('a,'b) -> process('b,'c) -> process('a,'c)
  | compose p1 (D # Output c p2) = D # Output c (compose p1 p2)
  | compose (D # Output b p1) (D # Input phi2) = compose p1 (D # phi2 b)
  | compose (D # Input phi1) p2 = D # Input $ compose_aux phi1 p2
and
  | compose_aux : ('a -> process_aux('a,'b,process('a,'b))) ->
                  process('b,'c) ->
                  'a ->
                  process_aux('a,'c,process('a,'c))
  | compose_aux phi1 p2 a = (compose (D # phi1 a) p2).D  --compose (D # phi1 a) ???



-- examples
-- the identity function as a stream processor
val id : process('x,'x)
  | id = D # Input id_aux
-- it would be nice to have lambdas:
--  | id = D # Input (fun x -> Output x id)
and
    id_aux : 'x -> process_aux('x,'x,process('x,'x))
  | id_aux x = Output x id


-- the "jump" function as a stream processes:
--   take the first element, remove that many elements
--   start over
val jump : process(nat,nat)
  | jump = D # Input jump_input
and
  | jump_input : nat -> process_aux(nat,nat,process(nat,nat))
  | jump_input 0 = Input output_aux         -- output the next element
  | jump_input (n+1) = Input $ jump_aux n   -- throw away the next element, start over
-- it would be nice to have lambdas:
--  | jump_input 0 = Input $ fun n -> Output n jump
--  | jump_input (n+1) = Input $ fun n _ -> jump_input n
and
  | jump_aux : nat -> nat -> process_aux(nat,nat,process(nat,nat))
  | jump_aux n _ = jump_input n
and
  | output_aux : nat -> process_aux(nat,nat,process(nat,nat))
  | output_aux n = Output n jump


-- the "partial sums" function as a stream processor:
--   take the first element, sum that number of following elements
--   start over
val partial_sums : process(nat,nat)
  | partial_sums = D # Input in_sums
and
  | in_sums : nat -> process_aux(nat,nat,process(nat,nat))
  | in_sums 0 = Output 0 partial_sums
  | in_sums (n+1) = sums_aux 0 (n+1)
and
    sums_aux : nat -> nat -> process_aux(nat,nat,process(nat,nat))
  | sums_aux acc 0 = Output acc partial_sums
  | sums_aux acc (n+1) = Input $ aux acc n
and
  | aux : nat -> nat -> nat -> process_aux(nat,nat,process(nat,nat))
  | aux acc n m = sums_aux (add acc m) n



-- tests
val nats = arith 0 1

val test1 = eating id nats
val test2 = eating id (arith 1 0)

val test3 = eating jump nats

val test4 = eating partial_sums nats

val test5 = eating (compose id id) nats

val test6 = eating (compose jump id) nats
val test7 = eating (compose id jump) nats

-- this grows too fast. I use the stream 0,0,0,1,2,3,4,5,6,7,...
-- composing jump with itself on this stream gives
-- 0,0,3,9,21,45,93,189 and then
-- 0,93,...
val znats = { Head = 0 ; Tail = nats }
val zznats = { Head = 0 ; Tail = znats }
val zzznats = { Head = 0 ; Tail = zznats }
val test8_aux = eating (compose jump jump) zzznats
val test8_1 = test8_aux.Head
val test8_2 = test8_aux.Tail.Head
-- later elements take too much time to compute...


val test9 = eating (compose partial_sums id) nats
val test10 = eating (compose id partial_sums) nats

