open Misc
exception Error of string

(* types for type expressions and substitutions *)
type type_name = string
type type_expression =
    | TVar of bool*string     (* polymorphic type variable, the boolean indicates if the variable can be instantiated *)
    | Data of type_name * (type_expression list)
    | Arrow of type_expression * type_expression
type type_substitution = (type_name * type_expression) list

(* unification on on types *)
let rec occur_type (x:type_name) (t:type_expression) = match t with
    | TVar(true,y) -> x=y
    | TVar(false,_) -> assert false
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Data(_, args) -> List.exists (occur_type x) args

let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression = match t with
    | TVar (true,y) -> (try List.assoc y sigma with Not_found -> t)
    | TVar _ -> t
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t1)
    | Data(a, args) -> Data(a, List.map (subst_type sigma) args)

let unify_type (t1:type_expression) (t2:type_expression) : type_substitution =
    let rec aux (eqs:(type_expression*type_expression) list ) = match eqs with
            | [] -> []
            | (s,t)::eqs when s=t -> aux eqs
            | (Data(t1, args1),Data(t2, args2))::eqs when t1=t2 ->
                begin
                    try aux ((List.combine args1 args2)@eqs)
                    with Invalid_argument _ -> raise Exit
                end
            | (t, TVar(true,x))::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    (x,t)::(aux eqs)
            | (TVar(true,x), t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    (x,t)::(aux eqs)
            | _ -> raise Exit
    in aux [ (t1,t2) ]

(* types for expressions, function definitions and environments *)
type arity = int
type priority = int
type const_name = string
type var_name = string

type term =
    | Var of string
    | Constant of const_name
    | Apply of term*term

type function_clause = term list * term
type bloc_nb = int      (* number of the block of mutual definitions *)
type environment = {
    current_priority: int                                                                   ;
    types:     (type_name * (type_name list) * priority * const_name list) list             ;
    constants: (const_name * priority * type_expression) list                               ;
    functions: (var_name * bloc_nb * type_expression * function_clause list) list           ;
    vars:      (var_name * type_expression) list                                            }

let get_arity (t:type_name) (env:environment) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _params, _, _)::_ when _t=t -> List.length _params
        | _::ts -> aux ts
    in
    aux env.types

let get_priority (t:type_name) (env:environment) : int =
    let rec aux = function
        | [] -> raise Not_found
        | (_t, _, _priority, _)::_ when _t=t -> _priority
        | _::ts -> aux ts
    in
    aux env.types

let get_type_const (c:const_name) (env:environment) =
    let rec aux = function
        | [] -> raise Not_found
        | (_c,_p,_t)::_ when _c=c -> _t
        | _::consts -> aux consts
    in aux env.constants

let get_type_var (x:var_name) (env:environment) =
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
    aux_var env.vars


let rec infer_type (u:term) (env:environment) : type_expression =
    match u with
        | Apply(u1,u2) ->
            begin
                let t1 = infer_type u1 env in
                let t2 = infer_type u2 env in
                match t1 with
                    | Arrow(t11,t12) ->
                            let sigma = unify_type t11 t2
                            in subst_type sigma t12
                    | _ -> raise Exit
            end
        | Constant(c) -> (try get_type_const c env with Not_found -> raise Exit)
        | Var(x) -> (try get_type_var x env with Not_found -> raise Exit)








