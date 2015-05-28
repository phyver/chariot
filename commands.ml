open Base

(* commands *)
type cmd =
    | Eof
    | Nothing
    | Cmd of string
    | TypeDef of priority * (type_name * arity * (term_constant * type_expression) list) list

