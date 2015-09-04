data t where A:t | B:t->t | C:t->t

:set collapse_graph true
:set show_initial_graph true

:set depth 3

val f1 (B (B (B (B x)))) = f1 (B (B (B (C x))))
  | f1 _ = ???

:set depth 4
val f2 (B (B (B (B x)))) = f2 (B (B (B (C x))))
  | f2 _ = ???

:set depth 8
val f3 (B (B (B (B x)))) = f3 (B (B (B (C x))))
  | f3 _ = ???

:set incremental_SCT false
val f4 (B (B (B (B x)))) = f4 (B (B (B (C x))))
  | f4 _ = ???
