:set depth 2
:set bound 1

:set allow_unsafe_defs false
:set collapse_graph true
:set use_subsumption false
:set continue_on_error true

-- :set show_initial_graph true
-- :set show_final_graph true
-- :set show_coherent_loops true
-- :set show_bad_loops true
-- :set show_all_steps true


data nat where Z : nat | S : nat -> nat

data list('a) where N : list('a) | C : 'a -> list('a) -> list('a)

val id : nat -> nat
  | id Z = Z
  | id (S n) = S (id n)

val di : nat -> nat
  | di n = di (S n)

val l : list('a) -> nat
  | l N = Z
  | l (C x xs) = S (l xs)


val ack Z n = S n
  | ack (S m) Z = ack m (S Z)
  | ack (S m) (S n) = ack m (ack (S m) n)

data tree('a) where Leaf : tree('a) | Node : tree('a) -> tree('a) -> tree('a)

val comb Leaf = Leaf
  | comb (Node t Leaf) = Node (comb t) Leaf
  | comb (Node t1 (Node t2 t3)) = comb (Node (Node t1 t2) t3)

val comb_size Leaf s = Leaf
  | comb_size (Node t Leaf) (S s) = Node (comb_size t s) Leaf
  | comb_size (Node t1 (Node t2 t3)) s = comb_size (Node (Node t1 t2) t3) s
  | comb_size (Node t Leaf) Z = ???


