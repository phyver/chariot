 -- rose trees
data rtree where Fork : list(rtree) -> rtree


-- size of a tree
val size : rtree -> nat
  | size (Fork Nil) = Zero
  | size (Fork (Cons t ts)) = add (size t) (size (Fork ts))

-- versions using map / fold_right / fold_left do not pass the test because the static analysis is too simple
-- (PML1 flow analysis would be better)
val size2 : rtree -> nat
  | size2 (Fork branches) = fold_left (fun a t -> a + (size2 t)) 0 branches

-- if we "inline" the specialized fold_left function, we obtain the following, which passes the totality test
val size3 : rtree -> nat
  | size3 (Fork branches) = fold 0 branches
and fold acc [] = acc
  | fold acc (b::bs) = fold (acc + (size3 b)) bs

