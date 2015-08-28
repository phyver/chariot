:set verbose 2
:set depth 2
:set bound 3

:set show_nats false

:test collapse f 0
:test collapse f 1
:test collapse f 2
:test collapse f 3
:test collapse f 4
:test collapse f 5

:test collapse f (B (B x1 x2) x3)
:test collapse f (B (B x1 x2) (B x3 x4))
:test collapse f (B (B x1 x2) (B x3 (B x4 x5)))
:test collapse f (B (B x1 x2) (B x3 (B x4 (S x5))))
:test collapse f (B (B x1 x2) (B x3 (B x4 (S (S x5)))))
:test collapse f (B (B x1 x2) (B x3 (B (B x4 x5) (B x6 x7))))
:test collapse f (B (B x1 x2) (B x3 (B (B x4 x5) (B x6 x5))))

:test collapse s
:test collapse s.Tail
:test collapse s.Tail.Tail
:test collapse s.Tail.Tail.Tail
:test collapse s.Tail.Tail.Tail.Tail
:test collapse s.Tail.Tail.Tail.Tail.Tail

:test collapse ((((t n1).Next n2 n3).Next n4 n5).Next n6 n7).Root
:test collapse ((((t (S(S(S n1)))).Next n2 n3).Next (S(S(S n4))) n5).Next n6 (S(S(S n7)))).Root


