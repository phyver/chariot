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
type priority = int option     (* priority of types and constants: odd for data and even for codata *)
type type_name = string
type type_expression =
    | TVar of type_name
    | Data of type_name * (type_expression list) * priority
    | Arrow of type_expression * type_expression
type type_substitution = (type_name * type_expression) list


(* type for expressions *)
type const_name = string
type var_name = string
type term =
    | Angel                                     (* generic meta variable, living in all types *)
    | Var of var_name
    | Const of const_name * priority            (* constructor, with a priority *)
    | Proj of const_name * priority             (* destructor, with a priority *)
    | App of term * term


type bloc_nb = int      (* number of the block of mutual function definitions *)

type pattern = term                                   (* a pattern (LHS of a clause in a definition) is just a special kind of term *)
type function_clause = pattern * term     (* clause of a function definition *)

(* type for the environment *)
type environment = {
    current_type_bloc: bloc_nb                                                              ;
    current_function_bloc: bloc_nb                                                           ;

    (* we keep the names of type arguments of a definition in the environment,
     * together with bloc number and the list of its constants
     * (constructors/destrucors)
     * The bloc number is even for codatatypes and odd for datatypes. *)
    types:     (type_name * (type_name list) * bloc_nb * const_name list) list             ;

    (* each constant (type constructor/destructor) has a type and a priority
     * the priority is either 0 for destructors or 1 for constructors *)
    constructors: (const_name * type_expression) list                               ;
    projections:  (const_name * type_expression) list                               ;

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

let is_data (env:environment) (t:type_name) : bool =
    let rec is_data_aux = function
        | [] -> raise Not_found
        | (_t, _, _n, _)::_ when _t=t -> _n mod 2 = 1
        | _::ts -> is_data_aux ts
    in
    is_data_aux env.types

let get_type_constants (env:environment) (t:type_name) : const_name list =
    let rec get_type_constants_aux = function
        | [] -> raise Not_found
        | (_t, _, _, _constants)::_ when _t=t -> _constants
        | _::ts -> get_type_constants_aux ts
    in
    get_type_constants_aux env.types

let get_constructor_type (env:environment) (c:const_name) =
    let rec get_type_constructors_aux = function
        | [] -> raise Not_found
        | (_c,_t)::_ when _c=c -> _t
        | _::consts -> get_type_constructors_aux consts
    in get_type_constructors_aux env.constructors

let get_projection_type (env:environment) (c:const_name) =
    let rec get_type_projections_aux = function
        | [] -> raise Not_found
        | (_c,_t)::_ when _c=c -> _t
        | _::consts -> get_type_projections_aux consts
    in get_type_projections_aux env.projections

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

(*
 * misc functions on types
 *)

(* get the rightmost type in a type *)
let rec get_result_type t = match t with
    | TVar _ | Data _ -> t
    | Arrow(_,t) -> get_result_type t

(* get the "leftmost" type in a type *)
let rec get_first_arg_type t = match t with
    | Arrow(t,_) -> t
    | t -> raise (Invalid_argument "get_first_arg_type")


(*
 * misc functions on terms
 *)

(* get the head of a term *)
let rec get_head v = match v with
    | Const _ | Angel | Var _ | Proj _ -> v
    | App(v,_) -> get_head v

(* get all the arguments of a term *)
let get_args v =
    let rec get_args_aux acc = function
        | Var _ | Const _ | Angel | Proj _ -> acc
        | App(v1,v2) -> get_args_aux (v2::acc) v1
    in get_args_aux [] v

(* get the head constructor of a term *)
let get_head_const v =
    match get_head v with
        | Const(c,_) -> c
        | _ -> raise (Invalid_argument "no head constructor")

(* get the function name from a pattern *)
let rec get_function_from_pattern v = match v with
    | Var f -> f
    | Const _ | Proj _ | Angel -> raise (Invalid_argument "no head function")
    | App(Proj _,v) -> get_function_from_pattern v
    | App(v,_) -> get_function_from_pattern v

(* apply a term to a list of arguments *)
let app (v:term) (args:term list) : term
 = List.fold_left (fun v arg -> App(v,arg)) v args
