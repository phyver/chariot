-- :set use_priorities false

:test compose
   f x y => g x x y y
and
   g a b l d => h b l


:test compose
   f x y => g (S x) (S (S (S (S x))))
and
   g a b => h a (T b)

:test compose
   f (S (S x))  => f x
and
   f (S x)  => f x

:test compose
  nats.P => nats
and
  nats.P => nats

:test compose
  nats.P.P => nats
and
  nats.P => nats

:test compose
  nats.P.P => nats
and
  nats.P.P.P => nats

:test compose
  nats => nats.P
and
  nats => nats.P

:test compose
  nats => nats.P.P
and
  nats => nats.P

:test compose
  nats => nats.P.P
and
  nats => nats.P.P


:test compose
   (f x).P y => g x
and
  (g x).Q y => f y

(* note: the last argument is dangling *)
:test compose
   ((f x).P y).P z => g x
and
  ((g x).Q y).Q z => f y

