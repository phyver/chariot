(*
 * operations on type and type inference
 *)
open Misc
open Base
open Pretty

(* apply a substitution on a type *)
let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression = match t with
    | TVar (y) -> (try List.assoc y sigma with Not_found -> t)
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t2)
    | Data(a, args) -> Data(a, List.map (subst_type sigma) args)

(* generate fresh variables *)
let fresh_variable_nb = ref 0
let reset_fresh_variable_generator () = fresh_variable_nb := 0
let fresh_variable () =
    let alpha = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] in
    let n = !fresh_variable_nb / 26 in
    let var = !fresh_variable_nb mod 26 in
    let x = (List.nth alpha var) ^ (if n = 0 then "" else (string_of_int n)) in
    incr fresh_variable_nb;
    TVar(x)

(* get all the variables from a type *)
let get_variables_from_type (t:type_expression) : type_name list =
    let rec get_variables_from_type_aux = function
        | TVar(x) -> [x]
        | Data(_, params) -> List.concat (List.map get_variables_from_type_aux params)
        | Arrow(t1,t2) -> (get_variables_from_type_aux t1) @ (get_variables_from_type_aux t2)
    in
    uniq (get_variables_from_type_aux t)

(* instantiate all the variables from a type with fresh variables *)
let instantiate_type (t:type_expression) : type_expression =
    let vars = get_variables_from_type t in
    let sigma = List.map (fun x -> (x,fresh_variable())) vars in
    subst_type sigma t

(* check if a variable occurs inside a type *)
let rec occur_type (x:type_name) (t:type_expression) : bool = match t with
    | TVar(y) -> x=y
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Data(_,args) -> List.exists (occur_type x) args

(*
 * unification of types
 *)

(* computes the most general unifier of t1 and t2
 * NOTE: priority is given to t1: if t2 is an instance t1, then the
 * substitution we compute doesn't affect t2 *)
let unify_type_mgu (t1:type_expression) (t2:type_expression) : type_substitution =
    message 4 (fun _ -> print_string "looking for mgu for ";
                        print_type t1; print_string " and ";
                        print_type t2; print_newline ());

    let rec mgu_aux (eqs:(type_expression*type_expression) list ) acc = match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> mgu_aux eqs acc
            | (Data(t1, args1),Data(t2, args2))::eqs when t1=t2 ->
                begin
                    try mgu_aux ((List.combine args1 args2)@eqs) acc
                    with Invalid_argument _ -> error ("datatype " ^ t1 ^ " appears with different arities")
                end
            | (Arrow(t1,t2),Arrow(s1,s2))::eqs -> mgu_aux ((t1,s1)::(t2,s2)::eqs) acc
            (* do not change order of next two cases *)
            | (t, TVar(x))::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    mgu_aux eqs ((x,t)::acc)
            | (TVar(x), t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    mgu_aux eqs ((x,t)::acc)
            | (TVar _,_)::_
            | (_,TVar _)::_ -> unificationError "cannot unify: loop"
            | (Arrow _,Data _)::_
            | (Data _,Arrow _)::_ -> unificationError "cannot unify arrow and data type"
            | (Data _, Data _)::_ -> unificationError "cannot unify different datatypes"
    in
    mgu_aux [ (t1,t2) ] []

(* unify the types t1 and t2 by applying the mgu to either one of them *)
let unify_type (t1:type_expression) (t2:type_expression) : type_expression =
    let sigma = unify_type_mgu t1 t2 in
    let _t1 = subst_type sigma t1 in
    let _t2 = subst_type sigma t2 in
    assert (_t1 = _t2);
    _t1

(* check if t1 is an instance of t2
 * NOTE: it relies on the mgu giving priority to its first argument *)
let is_instance t1 t2 =
    let sigma = unify_type_mgu t1 t2 in
    t1 = subst_type sigma t1

(* add one constraint into a sorted list of constraints *)
let rec add_constraint (x,t) constraints = match constraints with
    | [] -> [(x,t)]
    | (y,s)::_ when x<y -> (x,t)::constraints
    | (y,s)::constraints when x>y -> (y,s)::(add_constraint (x,t) constraints)
    | (y,s)::constraints (* when x=y *) -> (x,unify_type s t)::constraints

(* merge two sorted lists of constraints *)
let rec merge_constraints cs1 cs2 = match cs1,cs2 with
    | [],cs | cs,[] -> cs
    | (x1,t1)::cs1, (x2,_)::_ when x1<x2 -> (x1,t1)::(merge_constraints cs1 cs2)
    | (x1,_)::_, (x2,t2)::cs2 when x1>x2 -> (x2,t2)::(merge_constraints cs1 cs2)
    | (x1,t1)::cs1, (x2,t2)::cs2 (*when x1=x2*) -> (x1,unify_type t1 t2)::(merge_constraints cs1 cs2)

(* infers most general type of "u" in environment "env"
 * "vars" contains the type of functions that are currently being defined
 * the result is the type of the term together with a map giving the type of all the free variables
 *)
let infer_type (env:environment) (v:term) (constraints:(var_name*type_expression) list): type_expression*(var_name*type_expression) list =
    message 2 (fun _ -> print_string "infering type for ";
                        print_term v; print_newline());

    let rec
      (* infer the type of an atomic term:
       *    - for constructor: look in the environment
       *    - for variables: look in the environment, and if it doesn't exist,
       *      add a constraint
       *    - for a destructor: look in the environment and proceed as with an
       *      application *)
      infer_type_and_constraints_atomic (u:atomic_term) constraints
      : type_expression * (var_name * type_expression) list
      = match u with
            | Angel -> instantiate_type (TVar("angel")) , constraints
            | Var(x) ->
                begin
                    try List.assoc x constraints, constraints
                    with Not_found ->
                        try
                            let t = get_function_type env x in
                            (instantiate_type t, constraints)
                        with Not_found -> let t = TVar("type_"^x) in (t, add_constraint (x,t) constraints)
                end
            | Const(c,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        let p = get_constant_priority env c in
                        if p mod 2 = 0 then typeError (c ^ " is not a constructor");    (* FIXME: this should be done by a check_term function *)
                        (t , constraints)
                    with Not_found -> typeError ("cannot infer type of constant " ^ c)
                end
            | Proj(u,d,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        let p = get_constant_priority env d in
                        if p mod 2 = 1 then typeError (d ^ " is not a destructor");     (* FIXME: this should be done by a check_term function *)
                        check_type_single_application t u constraints
                    with Not_found -> typeError ("cannot infer type of constant " ^ d)
                end

    and

      (* check the type of an application of a function to an argument.
       *    - t is the type of the function
       *    - arg is the argument: its type should be the the same as the type
       *      on the left of the arrow of t *)
      check_type_single_application (t:type_expression) (arg:term) constraints
      : type_expression * (var_name * type_expression) list
      = let targ,constraints = infer_type_and_constraints_term arg constraints in
        let sigma= unify_type_mgu t (instantiate_type (Arrow(TVar("arg"),TVar("result")))) in
        let constraints = List.map (second (subst_type sigma)) constraints in
        let t = subst_type sigma t in
        let targ = subst_type sigma targ in
        match t with
            | Arrow(t1,t2) ->
                begin
                    let tau = unify_type_mgu t1 targ in
                    let constraints = List.map (second (subst_type tau)) constraints in
                    try (subst_type tau t2, constraints)
                    with UnificationError s -> typeError ("cannot type this term: " ^ s)
                end
            | _ -> typeError "not a function type!!!"

    and

      (* check the type of an atomic term applied to arguments
       * t is the type of the atomic term: it should be of the form t1 -> t2 -> ... -> tn -> r
       * where the length of args is n *)
      check_type_applications (t:type_expression) (args:term list) constraints
      : type_expression * (var_name * type_expression) list
      = match args with
            | [] -> t,constraints
            | arg::args -> let t,constraints = check_type_single_application t arg constraints in
                               check_type_applications t args constraints

    and

      (* infer the type of a term and gather constraints on free variables *)
      infer_type_and_constraints_term (App(u,args):term) constraints
      : type_expression * (var_name * type_expression) list
      = let tu,constraints = infer_type_and_constraints_atomic u constraints in
        match args with
            | [] -> tu,constraints
            | args ->
                let sigma= unify_type_mgu tu (instantiate_type (Arrow(TVar("arg1"),TVar("result")))) in
                let constraints = List.map (second (subst_type sigma)) constraints in
                let tu = subst_type sigma tu in
                check_type_applications tu args constraints
    in
    infer_type_and_constraints_term v constraints

