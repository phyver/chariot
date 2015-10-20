data bool where True | False : bool

val if True  a b = a
  | if False a b = b

data nat where Zero : nat | Succ : nat -> nat

val le 0 _ = True
  | le _ 0 = False
  | le (m+1) (n+1) = le m n

data tree('x) where Branch : tree('x) -> 'x -> tree('x) -> tree('x)

val
  | insert_t x (Branch l y r) =
        if (le x y)
        (Branch (insert_t y r) x l)
        (Branch (insert_t x r) y l)
