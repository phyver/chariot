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

type 'a atomic_term =
    | Daimon
    | Var of string
    | Const of const_name * 'a
    | Proj of 'a term * const_name * 'a
and
    'a term =
    | App of 'a atomic_term * 'a term list

let app (App(u,args1)) args2 = App(u,args1 @ args2)

type function_clause = priority term * priority term

type environment = {
    current_priority: priority                                                              ;
    current_bloc: int                                                                       ;
    types:     (type_name * (type_name list) * priority * const_name list) list             ;
    constants: (const_name * priority * type_expression) list                               ;
    functions: (var_name * bloc_nb * type_expression * function_clause list) list           }

let get_arity (env:environment) (t:type_name) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _params, _, _)::_ when _t=t -> List.length _params
        | _::ts -> aux ts
    in
    aux env.types

let get_type_priority (env:environment) (t:type_name) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _, _priority, _)::_ when _t=t -> _priority
        | _::ts -> aux ts
    in
    aux env.types

let get_constant_priority (env:environment) (c:const_name) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_c, _priority, _)::_ when _c=c -> _priority
        | _::cs -> aux cs
    in
    aux env.constants

let get_type_const (env:environment) (c:const_name) =
    let rec aux = function
        | [] -> raise Not_found
        | (_c,_p,_t)::_ when _c=c -> _t
        | _::consts -> aux consts
    in aux env.constants

let get_type_var (env:environment) (x:var_name) (vars:(var_name*type_expression)list) =
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

let get_clauses (env:environment) (f:var_name) =
    let rec aux_function = function
        | [] -> raise Not_found
        | (_f,_,_,clauses)::_ when _f=f -> clauses
        | _::fcts -> aux_function fcts
    in
    aux_function env.functions

(* get the function name from a pattern *)
let rec get_function_name (App(u,args)) = match u with
    | Const(c,_) -> error (c ^ " is not a function name")
    | Daimon -> error ("you cannot redefine the daimon")
    | Var f -> f
    | Proj(u,d,_) -> get_function_name u

