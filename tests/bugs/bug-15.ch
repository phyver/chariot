data nat where
    | Zero : nat

data c('a) where
    | C : 'a -> c('a)

codata nuY('x) where
    | Nu : nuY('x) -> c('x)

codata stream4 where
    | D4 : stream4 -> nuY(stream4)


val zeros4 = { D4 = { Nu = C zeros4 } }

val convert4 { D4 = { Nu = C s } } = 0

:set verbose 10
:show functions
:set verbose 1

-- ERROR
val test12 = convert4 zeros4
:unfold test12 , 0


