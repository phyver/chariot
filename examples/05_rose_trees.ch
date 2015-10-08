 -- rose trees
data rtree where Fork : list(rtree) -> rtree


-- size of a tree
val size : rtree -> nat
  | size (Fork Nil) = Zero
  | size (Fork (Cons t ts)) = add (size t) (size (Fork ts))

-- versions using map / fold_right / fold_left do not pass the test because the static analysis is too simple
-- (PML1 flow analysis would be better)



