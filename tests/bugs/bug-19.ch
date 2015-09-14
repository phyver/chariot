data plus('a,'b) where
    | Cons0 : 'a -> plus('a,'b)
    | Cons1 : 'b -> plus('a,'b)

