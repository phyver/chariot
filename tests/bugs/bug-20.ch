codata pair('x,'y) where
    | Fst : pair('x,'y) -> 'x
    | Snd : pair('x,'y) -> 'y

data t('x) where
    | C : 'x -> t('x)

:set expand_clauses true
val h  { Fst = C y ; Snd = { Fst = C z ; Snd = zs }} = z

:set verbose 2
:show h
