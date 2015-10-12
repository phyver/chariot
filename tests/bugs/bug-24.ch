data tree('a,'x) where
    | Branch :  'x -> ('a -> tree('a,'x)) -> tree('a,'x)

val
  | f (Branch x b) = Branch x $ g b
and
  | g b x = f ???

:show f
:show g

-- there was a problem when composing the Angel, giving an empty approximation...
