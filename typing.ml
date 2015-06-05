
open Base
open Misc

open Pretty

(* unification on on types *)
let rec occur_type (x:type_name) (t:type_expression) = match t with
    | TVar(y) -> x=y
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Data(_,args) -> List.exists (occur_type x) args

let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression = match t with
    | TVar (y) -> (try List.assoc y sigma with Not_found -> t)
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t2)
    | Data(a, args) -> Data(a, List.map (subst_type sigma) args)

(* unify two types, giving "priority" to "t1":
 * if t2 is more specialized than t1, then the substitution we compute doesn't affect t2 *)
let unify_type (t1:type_expression) (t2:type_expression) : type_substitution =
    let rec aux (eqs:(type_expression*type_expression) list ) acc = match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> aux eqs acc
            | (Data(t1, args1),Data(t2, args2))::eqs when t1=t2 ->
                begin
                    try aux ((List.combine args1 args2)@eqs) acc
                    with Invalid_argument _ -> error ("ERROR: datatype " ^ t1 ^ " appears with different arities")
                end
            | (Arrow(t1,t2),Arrow(s1,s2))::eqs -> aux ((t1,s1)::(t2,s2)::eqs) acc
            (* do not change order of next two cases *)
            | (t, TVar(x))::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    aux eqs ((x,t)::acc)
            | (TVar(x), t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    aux eqs ((x,t)::acc)
            | (TVar _,_)::_
            | (_,TVar _)::_ -> error "cannot unify: loop"
            | (Arrow _,Data _)::_
            | (Data _,Arrow _)::_ -> error "cannot unify arrow and data type"
            | (Data _, Data _)::_ -> error "cannot unify different datatypes"
    in aux [ (t1,t2) ] []

(* check if t1 is an instance of t2 *)
let is_instance t1 t2 =
    let sigma = unify_type t1 t2 in
    t1 = subst_type sigma t1

(* infers most general type of "u" in environment "env"
 * "vars" contains the type of functions that are currently being defined
 * the result is the type of the term together with a map giving the type of all the free variables
 *)
let new_nb = ref 0
let reset_fresh () = new_nb := 0
let fresh () = incr new_nb; TVar("x" ^ (string_of_int !new_nb))
let infer_type (env:environment) (u:'a term) (vars:(var_name*type_expression) list): type_expression*(var_name*type_expression) list =

(* print_string "infer_type for "; print_term u; print_newline(); *)

    let get_tvars t =
        let rec uniq acc = function
            | [] -> acc
            | [a] -> a::acc
            | a::b::l when a=b -> uniq acc (b::l)
            | a::b::l -> uniq (a::acc) (b::l)
        in
        let rec aux = function
            | TVar(x) -> [x]
            | Data(_, params) -> List.concat (List.map aux params)
            | Arrow(t1,t2) -> (aux t1) @ (aux t2)
        in
        uniq (List.sort compare (aux t)) []
    in
    let instantiate t =
        let vars = get_tvars t in
        let sigma = List.map (fun x -> (x,fresh())) vars in
        subst_type sigma t
    in
    let rec add_constraint (x,t) constraints = match constraints with
        | [] -> [(x,t)]
        | (y,s)::_ when x<y -> (x,t)::constraints
        | (y,s)::constraints when x>y -> (y,s)::(add_constraint (x,t) constraints)
        | (y,s)::constraints (* when x=y *) ->
                let sigma = unify_type t s in
                (x,subst_type sigma t)::constraints
    in



    let rec
      infer_type_and_constraints_atomic (u:'a atomic_term) constraints =
(* print_string "infer_type_and_constraints_atomic of "; print_atomic_term u; print_string "\n  with constraints "; print_list "-no constraint-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) vars; print_newline(); *)
        match u with
            | Angel -> instantiate (TVar("angel")) , constraints
            | Const(c,_) ->
                begin
                    try
                        instantiate (get_type_const env c) , constraints
                    with Not_found -> error ("cannot infer type of constant " ^ c)
                end
            | Var(x) ->
                begin
                    try
                        List.assoc x constraints, constraints
                    with Not_found ->
                        try
                            (instantiate (get_type_var env x) , constraints)
                        with Not_found -> TVar("type_"^x), add_constraint (x, TVar("type_"^x)) constraints
                end
            | Proj(u,d,_) ->
                begin
                    try
                        let td, constraints = instantiate (get_type_const env d) , constraints in
(* print_string d; print_string " td "; print_type env td; print_newline(); *)
(* print_string "constraints "; print_list "" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) constraints; print_newline(); *)
(* print_term u; print_newline(); *)
                        infer_type_and_constraints_application td u constraints

                    with Not_found -> error ("cannot infer type of constant " ^ d)
                end

    and

      infer_type_and_constraints_application (t:type_expression) (arg:'a term) constraints =
(* print_string "infer_type_and_constraints_application of "; print_term arg; print_string " with function type "; print_type env t; print_newline(); *)
        let targ,constraints = infer_type_and_constraints_term arg constraints in
(* print_string "targ "; print_type env targ; print_newline(); *)
        let sigma= unify_type t (instantiate (Arrow(TVar("'x"),TVar("'y")))) in
(* print_string "sigma "; print_list "" "" " ; " "" (function x,t -> print_string ("'" ^ x ^ "="); print_type env t) sigma; print_newline(); *)
        let constraints = List.map (second (subst_type sigma)) constraints in
        let t = subst_type sigma t in
(* print_string "constraints "; print_list "-no constraint-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) vars; print_newline(); *)
        let targ = subst_type sigma targ in
(* print_string "targ bis "; print_type env targ; print_newline(); *)

        match t with
            | Arrow(t1,t2) ->
                    let tau = unify_type t1 targ in
(* print_string "tau "; print_list "" "" " ; " "" (function x,t -> print_string ("'" ^ x ^ "="); print_type env t) tau; print_newline(); *)
                    let constraints = List.map (second (subst_type tau)) constraints in
(* print_string "constraints "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) constraints; print_newline(); *)

                    (try
                        subst_type tau t2 , constraints
                    with Error s -> error ("cannot type this term: " ^ s))
            | _ -> error "not a function type!!!"

    and
      infer_type_and_constraints_applications (t:type_expression) (args:'a term list) constraints =
(* print_string "infer_type_and_constraints_applications of "; print_list "" "" " , " "" print_term args; print_string "\n  with function type "; print_type env t; print_newline(); *)
          match args with
            | [] -> t,constraints
            | arg::args ->
                    let t,constraints = infer_type_and_constraints_application t arg constraints in
                    infer_type_and_constraints_applications t args constraints

    and
      infer_type_and_constraints_term (App(u1,args):'a term) constraints =
(* print_string "infer_type_and_constraints_term of "; print_term (App(u1,args)); print_newline(); *)
            let tu1,constraints = infer_type_and_constraints_atomic u1 constraints in
(* print_string "tu1 "; print_type env tu1; print_newline(); *)
            match args with
                | [] -> tu1,constraints
                | args ->
                    let sigma= unify_type tu1 (instantiate (Arrow(TVar("'x"),TVar("'y")))) in
                    let constraints = List.map (second (subst_type sigma)) constraints in
                    let tu1 = subst_type sigma tu1 in
                    infer_type_and_constraints_applications tu1 args constraints


    in infer_type_and_constraints_term u vars








