open Base

(* commands *)
type cmd =
    | Eof
    | Nothing
    | Cmd of string
    | TypeDef of priority * (type_name * arity * (const_name * type_expression) list) list

