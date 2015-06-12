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
type 'a special_term =
    | Angel                                     (* generic meta variable, living in all types *)
    | Var of var_name
    | Const of const_name * priority option     (* constructor, with a priority *)
    | Proj of const_name * priority option      (* destructor, with a priority *)
    | App of 'a special_term * 'a special_term
    | Special of 'a

type empty = { bot: 'a .'a }
type term = empty special_term

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
    (* TODO: use separate lists ? *)
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

let get_type_constants (env:environment) (t:type_name) : const_name list =
    let rec get_type_constants_aux = function
        | [] -> raise Not_found
        | (_t, _, _, _constants)::_ when _t=t -> _constants
        | _::ts -> get_type_constants_aux ts
    in
    get_type_constants_aux env.types

let get_constant_type (env:environment) (c:const_name) =
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
let rec get_head (v:term) = match v with
    | Const _ | Angel | Var _ -> v
    | App(Proj _,v) -> get_head v
    | App(v,_) -> get_head v
    | Proj _ -> assert false
    | Special v -> v.bot

let get_head_const v =
    match get_head v with
        | Const(c,_) -> c
        | _ -> error "no head constructor"

let rec get_function_name v =
    match get_head v with
        | Var(f) -> f
        | _ -> error "no head function"

