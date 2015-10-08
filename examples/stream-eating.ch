-- Hancock stream processors

:set verbose 1

-- infinite lists
codata stream('a) where
    | Head : stream('a) -> 'a
    | Tail : stream('a) -> stream('a)

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


-- example: they do not pass the totality test because the static analysis is too simple
-- PML1 flow analysis would solve the problem...
val id : process('x,'x)
  | id = D # Input in_id
and
    in_id : 'x -> process_aux('x,'x,process('x,'x))
  | in_id x = Output x id

data nat where
    | Zero : nat
    | Succ : nat -> nat

val add : nat -> nat -> nat
    | add m 0 = m
    | add m (n+1) = (add m n) + 1

val arith n r = { Head = n ; Tail = arith (add n r) r }

val test = eating id (arith 0 1)


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

val test2 = eating partial_sums (arith 0 1)
