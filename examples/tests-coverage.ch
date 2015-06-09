data nat where Zero : nat | Succ : nat -> nat

val add : nat -> nat -> nat
    | add n 0 = n
    | add n (m+1) = Succ (add n m)

val mult : nat -> nat -> nat
    | mult n 0 = 0
    | mult n (m+1) = n + (mult n m)

val pow : nat -> nat -> nat
    | pow n 0 = 1
    | pow n (m+1) = mult n (pow n m)

val ack 0 n = n+1
  | ack (m+1) 0 = ack m 1
  | ack (m+1) (n+1) = ack m (ack (m+1) n)

data
  list('x) where Nil : list('x)
              | Cons : 'x -> list('x) -> list('x)

val length : list('x) -> nat
    | length Nil = Zero
    | length (Cons x xs) = Succ (length xs)


(* rose trees *)
data rtree where Fork : list(rtree) -> rtree

(* size of a tree *)
val size : rtree -> nat
  | size (Fork Nil) = Zero
  | size (Fork (Cons t ts)) = add (size t) (size (Fork ts))


(* coinductive type: streams *)
codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)


  (* map on streams *)
val map : ('x -> 'y) -> stream('x) -> stream('y)
    | (map f s).Head = f (s.Head)
    | (map f s).Tail = map f s.Tail

val (fib n m).Head = n
  | (fib n m).Tail.Head = m
  | (fib n m).Tail.Tail = fib (n+m) (n+m+m)

(* oops... I need the booleans *)
data bool where True : bool | False : bool

(* and I can define mutually recursive functions" *)
val
  even : nat -> bool
      | even Zero = True
      | even (Succ n) = odd n
and
  odd : nat -> bool
      | odd Zero = False
      | odd (Succ n) = even n

(* streams *)
val arith : nat -> nat -> stream(nat)
  | (arith n r).Head = n
  | (arith n r).Tail = arith (add n r) r

val get_nth : nat -> stream('a) -> 'a
  | get_nth Zero s = s.Head
  | get_nth (Succ n) s = get_nth n s.Tail

val mappair f Nil ys = Nil
  | mappair f (Cons x xs) Nil = Nil
  | mappair f (Cons x xs) (Cons y ys) = Cons (f x y) (mappair f xs ys)

