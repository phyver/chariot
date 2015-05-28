open Base

(* commands *)
type cmd =
    | Eof
    | Nothing
    | Cmd of string

    | TypeDef of priority * (type_name * (type_expression list) * (const_name * type_expression) list) list
    (*
     * The output of a type definition from the parser consists of
     *   - a priority odd/even to distinguish data / codada types
     *   - a list of (possibly) mutual type definitions:
     *        - a type name
     *        - a list of type parameters, all of the form TVar(true,x)
     *        - a list of constants (constructors for data, destructors for codata), with a type
     * No sanity checking is done by the parser, everything is done in the "process_type_defs" function in file "checkTypes.ml"...
     *)

