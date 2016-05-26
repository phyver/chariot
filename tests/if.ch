data
  ifexp('a) where At : 'a -> ifexp('a)
                | If : ifexp('a) ->  ifexp('a) -> ifexp('a) -> ifexp('a)

-- :set show_coherent_loops true
-- :set show_bad_loops true
-- :set show_all_steps true
-- :set incremental_SCP false

val nm : ifexp('a) -> ifexp('a)
  | nm (At a) = At a
  | nm (If (At a) y z) = If (At a) (nm y) (nm z)
  | nm (If (If u v w) y z) = nm (If u (nm (If v y z)) (nm (If w y z)))

-- :show functions


