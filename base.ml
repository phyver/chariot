(*
 * the types for representing
 *   - types
 *   - terms
 *   - environments
 *)

exception Error of string
let error s = raise (Error s)

exception UnificationError of string
let unificationError s = raise (UnificationError s)

exception TypeError of string
let typeError s = raise (TypeError s)

let verbose = ref 0     (* for information messages *)
let message k m = if !verbose > k then (print_string (" " ^ (String.make k '-') ^ " "); m ())

(* types for type expressions and substitutions *)
type type_name = string
type type_expression =
    | TVar of type_name
    | Data of type_name * (type_expression list)
    | Arrow of type_expression * type_expression
type type_substitution = (type_name * type_expression) list


(* type for expressions *)
type const_name = string
type var_name = string
type priority = int     (* priority of types and constants: odd for data and even for codata *)
type atomic_term =
    | Angel                                    (* generic meta variable, living in all types *)
    | Var of var_name
    | Const of const_name * priority           (* constructor, with a priority *)
    | Proj of term * const_name * priority     (* destructor, necessarily applied to a term, with a priority *)
and
    term =
    | App of atomic_term * term list  (* actual terms are applications, possibly empty *)

(* helper function to apply a term to arguments *)
let app (App(u,args1)) args2 = App(u,args1 @ args2)


type bloc_nb = int      (* number of the block of mutual function definitions *)

type pattern = term                                   (* a pattern (LHS of a clause in a definition) is just a special kind of term *)
type function_clause = pattern * term     (* clause of a function definition *)

(* type for the environment *)
type environment = {
    current_priority: priority                                                              ;
    current_bloc: int                                                                       ;

    (* we keep the names of type arguments of a definition in the environment,
     * together with its priority and the list of its constants
     * (constructors/destrucors) *)
    types:     (type_name * (type_name list) * priority * const_name list) list             ;

    (* each constant (type constructor/destructor) has a type and a priority *)
    constants: (const_name * priority * type_expression) list                               ;

    (* each function is defined inside a bloc of definitions and has a type and
     * a list of defining clauses *)
    functions: (var_name * bloc_nb * type_expression * function_clause list) list           }

(*
 * some utility functions
 *)
let get_type_arity (env:environment) (t:type_name) : int =
    let rec get_type_arity_aux = function
        | [] -> raise Not_found
        | (_t, _params, _, _)::_ when _t=t -> List.length _params
        | _::ts -> get_type_arity_aux ts
    in
    get_type_arity_aux env.types

let get_type_priority (env:environment) (t:type_name) : int =
    let rec get_type_priority_aux = function
        | [] -> raise Not_found
        | (_t, _, _priority, _)::_ when _t=t -> _priority
        | _::ts -> get_type_priority_aux ts
    in
    get_type_priority_aux env.types

let get_type_constants (env:environment) (c:const_name) =
    let rec get_type_constants_aux = function
        | [] -> raise Not_found
        | (_c,_p,_t)::_ when _c=c -> _t
        | _::consts -> get_type_constants_aux consts
    in get_type_constants_aux env.constants

let get_constant_priority (env:environment) (c:const_name) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_c, _priority, _)::_ when _c=c -> _priority
        | _::cs -> aux cs
    in
    aux env.constants

let get_function_type (env:environment) (x:var_name) =
    let rec get_function_type_aux = function
        | [] -> raise Not_found
        | (f,_,t,_)::_ when f=x -> t
        | _::fcts -> get_function_type_aux fcts
    in
    get_function_type_aux env.functions

let get_function_clauses (env:environment) (f:var_name) =
    let rec get_function_clauses_aux = function
        | [] -> raise Not_found
        | (_f,_,_,clauses)::_ when _f=f -> clauses
        | _::fcts -> get_function_clauses_aux fcts
    in
    get_function_clauses_aux env.functions

(* get the function name from a pattern *)
let rec get_function_name (p:pattern) =
    let  App(u,args) = p in
    match u with
    | Const(c,_) -> error (c ^ " is not a function name")
    | Angel -> error ("you cannot redefine the angel")
    | Var f -> f
    | Proj(u,d,_) -> get_function_name u

