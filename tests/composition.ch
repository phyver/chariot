
:testcompose
   f x y => g x x y y
and
   g a b c d => h b c


:testcompose
   f x y => g (S x) (S (S (S (S x))))
and
   g a b => h a (T b)

:testcompose
   f (S (S x))  => f x
and
   f (S x)  => f x

:testcompose
  nats.P => nats
and
  nats.P => nats

:testcompose
  nats.P.P => nats
and
  nats.P => nats

:testcompose
  nats.P.P => nats
and
  nats.P.P.P => nats

:testcompose
  nats => nats.P
and
  nats => nats.P

:testcompose
  nats => nats.P.P
and
  nats => nats.P

:testcompose
  nats => nats.P.P
and
  nats => nats.P.P


:testcompose
   (f x).P y => g x
and
  (g x).Q y => f y

(* note: the last argument is dangling *)
:testcompose
   ((f x).P y).P z => g x
and
  ((g x).Q y).Q z => f y

