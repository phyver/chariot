data c('x) where C1 : 'x -> c('x)
codata t1 where D1 : t1 -> c(t1)

codata d('x) where D2 : d('x) -> 'x
data t2 where C2 : d(t2) -> t2

val test1 : t1
  | test1 = D1 # C1 $ test1

val test2 : t2
  | test2 = C2 $ D2 # test2
