data c('x) where C1 : 'x -> c('x)
codata t1 where D1 : t1 -> c(t1)

codata d('x) where D2 : d('x) -> 'x
data t2 where C2 : d(t2) -> t2

val test1 : t1
  | test1 = D1 # C1 $ test1

val test2 : c(t1)
    | test2 = C1 $ D1 # test2

val test3 : t2
  | test3 = C2 $ D2 # test3

val test4 : d(t2)
    | test4 = D2 # test3

:show functions

