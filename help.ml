let help_text = [
  "    Chariot";
  "    =======";
  "";
  "    A language with arbitrary nested inductive and coinductive types";
  "    ================================================================";
  "";
  "";
  "Types";
  "-----";
  "";
  "Types come in two flavors: strict/inductive or lazy/coinductive.";
  "";
  "A strict type is defined with";
  "    data tname(params)";
  "    where C1 : t0 -> t1 -> ... -> tname(params)";
  "        | C2 : ...";
  "        | ...";
  "";
  "Each Ci is a *constructor* and its type must end with tname(params).";
  "(Each of the tj can also be tname(params) in order to define an";
  "inductive type.)";
  "";
  "For example";
  "    data nat";
  "    where Zero : nat";
  "        | Succ : nat -> nat";
  "";
  "    data list('a)";
  "    where Nil : list('a)";
  "        | Cons : 'a -> list('a) -> list('a)";
  "";
  "    data empty";
  "    where";
  "        -- no constructor!";
  "";
  "";
  "A lazy type is defined with";
  "    codata tname(params)";
  "    where D1 : tname(params) -> t1 -> t2 -> ... -> t3";
  "        | D2 : ...";
  "        | ...";
  "";
  "Each Ci is a *destructor* and its type must start with tname(params).";
  "(Each of the tj can also be tname(params in order to define a";
  "coinductive type.)";
  "There cannot be 'nullary' destructors D : tname(params).";
  "";
  "For example";
  "    codata stream('x)";
  "    where Head : stream('x) -> 'x";
  "        | Tail : stream('x) -> stream('x)";
  "";
  "    codata prod('a,'b)";
  "    where Fst : prod('a,'b) -> 'a";
  "        | Snd : prod('a,'b) -> 'b";
  "";
  "    codata one";
  "    where";
  "        -- no destructor!";
  "";
  "    codata tree('b,'x)      -- infinite trees branching on 'b with data in 'x";
  "    where Root : tree('b,'x) -> 'x";
  "        | Branch : tree('b,'x) -> 'b -> tree('b,'x)";
  "";
  "";
  "Note: to define a coinductive type with several 'constructors', we have";
  "to define an auxiliary strict parametrized type:";
  "";
  "    data colist_aux('x,'l)";
  "    where Nil : colist_aux('x,'l)";
  "        | Cons : 'x -> 'l -> colist_aux('x,'l)";
  "    codata colist('x)";
  "    where D : colist('x) -> colist_aux('x,colist('x))";
  "";
  "or";
  "";
  "    data process_aux('p)";
  "    where End : process_aux('p)";
  "        | Out : nat -> process_aux('p)";
  "        | In : nat -> (nat -> 'p) -> process_aux('p)";
  "    codata process";
  "    where D : process -> process_aux(process)";
  "";
  "(Beware that no two constructors / destructor may have the same name!)";
  "";
  "";
  "";
  "Definitions";
  "-----------";
  "";
  "A definition is of the form";
  "    val f : t1 -> t2 -> ... -> tn";
  "      | clause0 = def0";
  "      | clause1 = def1";
  "      | ...";
  "";
  "Each clause is itself of the form";
  "        ((f cp ... cp).D cp ... cp).D ...";
  "where each cp is a pattern (à la ML / Miranda).";
  "    cp ::= _ | var | C cp ... cp | { D = cp ; ... ; D = cp }";
  "";
  "Each def is a term:";
  "    term ::= var | (term) | term term | C | term.D | { D = term ; ... ; D = term }";
  "";
  "Some additionnal terms are";
  "  - ??? for a 'generic' metavariable";
  "  - !!! for a 'generic exception'";
  "Those terms can take any type and differ only in how they behave during";
  "evaluation / adequacy checking.";
  "";
  "The type will be infered if not given. It is only necessary for";
  "functions with 0 clause.";
  "";
  "For example:";
  "    val add n Zero = n";
  "      | add n (Succ m) = Succ (add n m)";
  "";
  "    val bot : empty -> 'a";
  "";
  "    val map : ('a -> 'b) -> list('a) -> list('b)";
  "      | map _ Nil = Nil";
  "      | map f (Cons x xs) = Cons (f x) (map f xs)";
  "";
  "    val (map_stream f s).Head = f (s.Head)";
  "      | (map_stream f s).Tail = map_stream f (s.Tail)";
  "";
  "    val branch : tree('b,'x) -> list('b) -> list('x)";
  "      | branch t Nil = t.Root";
  "      | branch t (Cons b bs) = Cons (t.Root) (branch (t.Branch b) bs)";
  "";
  "";
  "Note that structures { D = ... ; ... ; D = ... } are never necessary and";
  "can be replaced by auxiliary functions.";
  "Structure are nevertheless necessary to avoid loosing too much";
  "information for adequacy checking.";
  "";
  "";
  "Syntactic sugar";
  "---------------";
  "";
  "Several syntactic sugar are available:";
  "  - a decimal integer is expanded to Succ (Succ ... Zero)";
  "  - 'term + k' is expandend to Succ (Succ ... term)";
  "  - $ can be used for left-associative application";
  "  - a structure with a single label (destructor) D can be written as";
  "    with a #:";
  "        D # term    instead of { D = term }";
  "  - lists can be given using Caml notation";
  "";
  "    val fib 0 = 0";
  "      | fib 1 = 1";
  "      | fib (n+2) = add (fib (n+1)) (fib n)";
  "";
  "    val rev_append [] l = l";
  "      | rev_append (x::xs) l = rev_append xs (x::l)";
  "";
  "";
  ]