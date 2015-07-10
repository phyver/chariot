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
type priority = int option    (* priority of types and constants: odd for data and even for codata *)
type 'a special_term =
    | Angel                                     (* generic meta variable, living in all types *)
    | Var of var_name
    | Const of const_name * priority    (* constructor, with a priority *)
    | Proj of const_name * priority     (* destructor, with a priority *)
    | App of 'a special_term * 'a special_term
    | Special of 'a

type empty = { bot: 'a .'a }
type term = empty special_term

type bloc_nb = int      (* number of the block of mutual function definitions *)

type pattern = term                                   (* a pattern (LHS of a clause in a definition) is just a special kind of term *)
type function_clause = pattern * term     (* clause of a function definition *)

(* type for the environment *)
type environment = {
    current_type_bloc: int          (* counter for blocs of type definitions: odd for data and even for codata *) ;
    current_function_bloc: int                                                         ;

    (* we keep the names of type arguments of a definition in the environment,
     * together with its bloc number and the list of its constants
     * (constructors/destrucors) *)
    types:     (type_name * (type_name list) * int * const_name list) list             ;

    (* each constant (type constructor/destructor) has a type and a bloc number
     * the bloc number is odd for constructors and even for destructors *)
    (* TODO: use separate lists ? *)
    constants: (const_name * int * type_expression) list                               ;

    (* each function is defined inside a bloc of definitions and has a type and
     * a list of defining clauses *)
    functions: (var_name * bloc_nb * type_expression * function_clause list) list      }

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

let is_inductive (env:environment) (t:type_name) : bool =
    let rec is_inductive_aux = function
        | [] -> raise Not_found
        | (_t, _, _n, _)::_ when _t=t -> _n mod 2 = 1
        | _::ts -> is_inductive_aux ts
    in
    is_inductive_aux env.types

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

let is_projection (env:environment) (c:const_name) : bool =
    let rec aux = function
        | [] -> raise Not_found
        | (_c, _n, _)::_ when _c=c -> _n mod 2 = 0
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
let rec get_head (v:'a special_term) = match v with
    | Const _ | Angel | Var _ | Proj _ | Special _ -> v
    | App(v,_) -> get_head v

let rec get_head_const v = match v with
    | Const(c,p)  -> c
    | Angel | Var _ | Proj _ | Special _ ->  raise (Invalid_argument "no head constructor")
    | App(v,_) -> get_head_const v

let rec get_function_name v = match v with
    | Var f -> f
    | Angel | Const _ | Proj _ ->  raise (Invalid_argument "no head function")
    | App(Proj _,v) -> get_function_name v
    | App(v,_) -> get_function_name v
    | Special v -> v.bot

let get_args v =
    let rec get_args_aux acc = function
        | Const _ | Angel | Var _ | Proj _ | Special _ -> acc
        | App(v1,v2) -> get_args_aux (v2::acc) v1
    in
    get_args_aux [] v

let app f args = List.fold_left (fun t arg -> App(t,arg)) f args

let rec get_result_type t = match t with
    | Data _ | TVar _ -> t
    | Arrow(_,t) -> get_result_type t

let rec get_args_type t = match t with
    | Data _ | TVar _ -> []
    | Arrow (t1,t2) -> t1::(get_args_type t2)

let get_first_arg_type t = match t with
    | Data _ | TVar _ -> raise (Invalid_argument "get_first_arg_type")
    | Arrow(t,_) -> t


let extract_type_variables t =
    let rec extract_type_variables_aux acc = function
        | TVar(x) -> x::acc
        | Data(_,params) -> List.fold_left (fun acc t -> extract_type_variables_aux acc t) acc params
        | Arrow(t1,t2) -> let acc = extract_type_variables_aux acc t1 in extract_type_variables_aux acc t2
    in extract_type_variables_aux [] t

let rec extract_atomic_types t = match t with
    | TVar _ -> [t]
    | Data(_,params) -> t::(List.concat (List.map extract_atomic_types params))
    | Arrow(t1,t2) -> (extract_atomic_types t1) @ (extract_atomic_types t2)
