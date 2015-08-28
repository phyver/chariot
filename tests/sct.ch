:set use_SCT true
:set verbose 1
:set depth 2
:set bound 1

:set allow_inadequate_defs false
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
-- :show id

val di : nat -> nat
  | di n = di (S n)
-- :show di

val l : list('a) -> nat
  | l N = Z
  | l (C x xs) = S (l xs)
-- :show l


val ack Z n = S n
  | ack (S m) Z = ack m (S Z)
  | ack (S m) (S n) = ack m (ack (S m) n)
-- :show ack

