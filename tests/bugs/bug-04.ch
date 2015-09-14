(* constructors in pattern should be fully applied *)
data t where A : t->t

val test A = A
