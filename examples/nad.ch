(* example from Thorsten and Nilse *)

codata stream('x) where
    | Head : stream('x) -> 'x
    | Tail : stream('x) -> stream('x)

data tree where
    | Node : stream(tree) -> tree

val bad.Head = Node bad
  | bad.Tail = bad

val worse = Node bad
