-- original example from Thorsten and Nilse

codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

-- this type should be empty!
data tree where
    | Node : stream(tree) -> tree

val bad : stream(tree)
  | bad.Head = Node bad
  | bad.Tail = bad

val t : tree
  | t = Node bad

:show bad

