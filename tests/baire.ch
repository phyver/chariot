:set verbose 1

data nat where
    | Zero : nat
    | Succ : nat -> nat

-- 'b: branching, 'x: data
codata tree('b,'x) where
    | Root : tree('b,'x) -> 'x
    | Next : tree('b,'x) -> 'b -> tree('b,'x)

val ones.Root = 1
  | ones.Next _ = ones

val t.Root = 0
  | (t.Next 0).Root = 0
  | (t.Next (n+1)).Root = 1
  | (t.Next 0).Next m = t
  | (t.Next (n+1)).Next m = ones
