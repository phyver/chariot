-- problem with idempotent loops...
-- Invalid_argument("decreasing should only be called on idempotent rules")

:set verbose 1
:set show_lists false

data list_aux('a,'l) where Nil : list_aux('a,'l) | Cons : 'a -> 'l -> list_aux('a,'l)

codata colist('a) where Unfreeze : colist('a) -> list_aux('a,colist('a))

val map : ('a → 'b) → colist('a) → colist('b)
  | (map f s).Unfreeze = map_aux f s.Unfreeze
and
    map_aux : ('a → 'b) → list_aux('a,colist('a)) → list_aux('b,colist('b))
  | map_aux f (Nil) = Nil
  | map_aux f (Cons x s) = Cons (f x) (map f s)

:show functions
