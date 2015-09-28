(* coinductive type: streams *)
codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)


(* map on streams *)
val map_stream f { Head = x ; Tail = s } = { Head = f x ; Tail = map_stream f s }

val arith n r = { Head = n ; Tail = arith (add n r) r }

val rev_list_stream_append [] s = s
  | rev_list_stream_append (x::xs) s = { Head = x ; Tail = rev_list_stream_append xs s }

val list_stream_append l s = rev_list_stream_append (rev l) s


-- not productive (stream of empty lists)
val stream_concat : stream(list('x)) -> stream('x)
  | stream_concat { Head = l ; Tail = s } = list_stream_append l (stream_concat s)

val sum_prefixes : stream(nat) -> stream(nat)
  | sum_prefixes { Head = n ; Tail = s } = sum_prefixes_aux n 0 s
and sum_prefixes_aux 0 acc s = { Head = acc ; Tail = sum_prefixes s }
  | sum_prefixes_aux (k+1) acc { Head = n ; Tail = s } = sum_prefixes_aux k (add n acc) s

val sums : stream(list(nat)) -> stream(nat)
| sums { Head = [] ; Tail = s } = { Head = 0 ; Tail = sums s }
| sums { Head = [n] ; Tail = s } = { Head = n ; Tail = sums s }
| sums { Head = n::m::l ; Tail = s } = sums { Head = (add n m)::l ; Tail = s }
