:verbose 0

(* type of natural numbers *)
data nat where Zero : nat | Succ : nat -> nat

(* type of lists and branching trees *)
data
  list('x) where Nil : list('x)
              | Cons : 'x -> list('x) -> list('x)
and
  tree('b,'x,'y) where
    | Leaf : 'y → tree('b,'x,'y)
    | Node : 'x → ('b → tree('b,'x,'y)) → tree('b,'x,'y)

(* length of a list *)
val length : list('x) -> nat
    | length Nil = Zero
    | length (Cons x xs) = Succ (length xs)

(* addition of natural numbers *)
val add : nat -> nat -> nat
    | add n 0 = n
    | add n (m+1) = Succ (add n m)

val mult : nat -> nat -> nat
    | mult n 0 = 0
    | mult n (m+1) = n + (mult n m)

val pow : nat -> nat -> nat
    | pow n 0 = 1
    | pow n (m+1) = mult n (pow n m)



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

(* using the angel *)
val oops : 'a -> 'b
  | oops a = ???

val oops2 : 'a -> 'b
  | oops2 = ???


(* show all the defined types *)
:show types

(* show all the defined functions *)
:show functions

(* test compute *)
: pow 3 (pow 2 2)


(* streams *)
val arith : nat -> nat -> stream(nat)
  | (arith n r).Head = n
  | (arith n r).Tail = arith (add n r) r

val get_nth : nat -> stream('a) -> 'a
  | get_nth Zero s = s.Head
  | get_nth (Succ n) s = get_nth n s.Tail


val double : nat -> nat | double n = mult n 2

: get_nth (mult 3 3) (map double (arith 3 3))

: map double (arith 3 3)

val compose : ('a -> 'a) -> ('a ->'a) -> 'a -> 'a
    | compose f g x = f (g x)

val twice : ('a -> 'a) -> ('a ->'a)
    | twice f = compose f f

val fourtimes : ('a -> 'a) -> ('a ->'a)
    | fourtimes = twice twice

: fourtimes double 2

val k x y = x

:verbose 0

val nats = map (arith 0) (arith 0 1)

