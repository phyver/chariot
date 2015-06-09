
data bool where True | False : bool

val lnot True = False | lnot False = True

val land True True = True
  | land _ _ = False

val lor False False = False
  | lor _ _ = True


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


data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val length : list('x) -> nat
    | length Nil = Zero
    | length (Cons x xs) = Succ (length xs)

val map f Nil = Nil
  | map f (Cons x xs) = Cons (f x) (map f xs)

val fold_right f Nil o = o
  | fold_right f (Cons x xs) o = f x (fold_right f xs o)

val fold_left f o Nil = o
  | fold_left f o (Cons x xs) = fold_left f (f o x) xs


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
val map_stream : ('x -> 'y) -> stream('x) -> stream('y)
    | (map_stream f s).Head = f (s.Head)
    | (map_stream f s).Tail = map_stream f s.Tail

codata lazy('a) where Unfreeze : lazy('a) -> 'a

val freeze : 'a -> lazy('a)
  | (freeze x).Unfreeze = x
