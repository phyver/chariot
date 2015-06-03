open Misc

exception Error of string
let error s = raise (Error s)


(* types for type expressions and substitutions *)
type type_name = string
type type_expression =
    | TVar of type_name
    | Data of type_name * (type_expression list)
    | Arrow of type_expression * type_expression
type type_substitution = (type_name * type_expression) list


(* types for expressions, function definitions and environments *)
type arity = int
type priority = int
type const_name = string
type var_name = string
type bloc_nb = int      (* number of the block of mutual definitions *)

type term =
    | Daimon
    | Var of string
    | Const of const_name
    | Proj of const_name
    | Apply of term*term

type function_clause = term * term
type environment = {
    current_priority: int                                                                   ;
    current_bloc: int                                                                       ;
    types:     (type_name * (type_name list) * priority * const_name list) list             ;
    constants: (const_name * priority * type_expression) list                               ;
    functions: (var_name * bloc_nb * type_expression * function_clause list) list           }

let get_arity (t:type_name) (env:environment) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _params, _, _)::_ when _t=t -> List.length _params
        | _::ts -> aux ts
    in
    aux env.types

let get_type_priority (t:type_name) (env:environment) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _, _priority, _)::_ when _t=t -> _priority
        | _::ts -> aux ts
    in
    aux env.types

let get_constant_priority (c:const_name) (env:environment) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_c, _priority, _)::_ when _c=c -> _priority
        | _::cs -> aux cs
    in
    aux env.constants

let get_type_const (c:const_name) (env:environment) =
    let rec aux = function
        | [] -> raise Not_found
        | (_c,_p,_t)::_ when _c=c -> _t
        | _::consts -> aux consts
    in aux env.constants

let get_type_var (x:var_name) (vars:(var_name*type_expression)list) (env:environment) =
    let rec aux_function = function
        | [] -> raise Not_found
        | (f,_,t,_)::_ when f=x -> t
        | _::fcts -> aux_function fcts
    in
    let rec aux_var = function
        | [] -> aux_function env.functions
        | (_x,_t)::_ when _x=x -> _t
        | _::vars -> aux_var vars
    in
    aux_var vars

let get_clauses (f:var_name) (env:environment) =
    let rec aux_function = function
        | [] -> raise Not_found
        | (_f,_,_,clauses)::_ when _f=f -> clauses
        | _::fcts -> aux_function fcts
    in
    aux_function env.functions

(* get the function name from a pattern *)
let rec get_function_name = function
    | Var(f) -> f
    | Const c | Proj c -> error (c ^ " is not a function name")
    | Daimon -> error ("you cannot redefine the daimon")
    | Apply(Proj _, p) -> get_function_name p       (* the constant should be a projection *)
    | Apply(p,_) -> get_function_name p

