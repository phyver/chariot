data list('x) where
    | Nil : list('x)
    | Cons : 'x -> list('x) -> list('x)

val length : list('x) -> nat
    | length [] = 0
    | length (x::xs) = (length xs) + 1

val map_list f [] = []
  | map_list f (x::xs) = (f x)::(map_list f xs)

val fold_right f [] o = o
  | fold_right f (x::xs) o = f x (fold_right f xs o)

val fold_left f o [] = o
  | fold_left f o (x::xs) = fold_left f (f o x) xs

val last [] = !!!
  | last [x] = x
  | last _::l = last l

val append [] l = l
  | append (x::xs) l = x::(append xs l)

val rev_append [] l = l
  | rev_append (x::xs) l = rev_append xs (x::l)

val rev l = rev_append l []

val concat [] = []
  | concat l::ls = append l (concat ls)
