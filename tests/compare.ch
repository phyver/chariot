:set use_priorities false

:echo "TRUE means that the first pattern is an approximation of the second"

:echo "expect TRUE"
:test compare f x => g x and  f x => g x

:echo "expect FALSE"
:test compare f x => g (S x) and  f x => g x

:echo "expect FALSE"
:test compare f x => g x and  f x => g (S x)

:echo "expect FALSE"
:test compare f (S x) => g x and  f x => g x

:echo "expect FALSE"
:test compare f x => g x and  f (S x) => g x


:set depth 0

:echo "expect TRUE"
:test compare f (S x) => g (S x) and  f (S x) => g (S x)

:echo "expect TRUE"
:test compare f (S x) => g (S (S x)) and  f (S x) => g (S x)

:echo "expect FALSE"
:test compare f (S x) => g (S x) and  f (S x) => g (S (S x))

:set depth 1

:echo "expect TRUE"
:test compare f (S x) => g (S x) and  f (S x) => g (S x)

:echo "expect TRUE"
:test compare f (S x) => g (S (S x)) and  f (S x) => g (S x)

:echo "expect FALSE"
:test compare f (S x) => g (S x) and  f (S x) => g (S (S x))


:echo "expect TRUE"
:test compare f x y => g x y  and  f x y => g x y

:echo "expect TRUE"
:test compare f x y => g x y  and  f x => g x

:echo "expect TRUE"
:test compare f x => g x  and  f x y => g x y

:echo "expect FALSE"
:test compare f x y => g x y  and  f x y => g x

:echo "expect FALSE"
:test compare f x y => g x y  and  f x y => g x x

:echo "expect FALSE"
:test compare f x y => g x y  and  f x y => g y x

:echo "expect FALSE"
:test compare f x y => g x y  and  f x y => g x (S y)

:echo "expect FALSE"
:test compare f (S x) y => g x y  and  f x y => g x y


:set depth 0

:echo "expect FALSE"
:test compare f x y => g x y  and  f x y => g x (S y)

:echo "expect FALSE"
:test compare f (S x) y => g x y  and  f x y => g x y

:echo "expect TRUE"
:test compare f x y => g (S x) y  and  f x y => g x y

:echo "expect FALSE"
:test compare f x y => g x y  and  f x (S y) => g x y

:echo "expect TRUE"
:test compare f x y => g (S x) y  and  f (S x) y => g x y

:echo "expect FALSE"
:test compare  f (S x) y => g y x and f x y => g (S x) y


:echo "expect FALSE"
:test compare f (S x) => g x  and  f x => g x

:echo "expect TRUE"
:test compare f x => g (S x)  and  f x => g x


