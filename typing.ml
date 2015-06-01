
open Base
open Misc
open Pretty

(* unification on on types *)
let rec occur_type (x:type_name) (t:type_expression) = match t with
    | TVar(y) -> x=y
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Data(_, args) -> List.exists (occur_type x) args

let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression = match t with
    | TVar (y) -> (try List.assoc y sigma with Not_found -> t)
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t2)
    | Data(a, args) -> Data(a, List.map (subst_type sigma) args)

let unify_type (t1:type_expression) (t2:type_expression) : type_substitution =
    let rec aux (eqs:(type_expression*type_expression) list ) acc = match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> aux eqs acc
            | (Data(t1, args1),Data(t2, args2))::eqs when t1=t2 ->
                begin
                    try aux ((List.combine args1 args2)@eqs) acc
                    with Invalid_argument _ -> raise (Error ("ERROR: datatype " ^ t1 ^ " appears with different arities"))
                end
            | (Arrow(t1,t2),Arrow(s1,s2))::eqs -> aux ((t1,s1)::(t2,s2)::eqs) acc
            | (t, TVar(x))::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    aux eqs ((x,t)::acc)
            | (TVar(x), t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    aux eqs ((x,t)::acc)
            | (TVar _,_)::_
            | (_,TVar _)::_ -> raise  (Error "cannot unify: loop")
            | (Arrow _,Data _)::_
            | (Data _,Arrow _)::_ -> raise (Error "cannot unify arrow and data type")
            | (Data _, Data _)::_ -> raise (Error "cannot unify different datatypes")
    in aux [ (t1,t2) ] []



(* infers most general type of "u" in environment "env"
 * "vars" contains the type of functions that are currently being defined
 * the result is the type of the term together with a map giving the type of all the free variables
 *)
let infer_type (u:term) (env:environment) (vars:(var_name*type_expression) list): type_expression*(var_name*type_expression) list =

    let new_nb = ref 0 in
    let fresh () = incr new_nb; TVar("x" ^ (string_of_int !new_nb)) in
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



    let rec aux u constraints =
        (* print_string "infer type of "; print_term u; print_string "\n  with constraints "; print_list "-no constraint-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) vars; print_newline(); *)
        match u with
            | Constant(c) -> (try instantiate (get_type_const c env) , constraints with Not_found -> raise (Error ("*** cannot infer type of constant " ^ c)))
            | Var(x) ->
                begin
                    try
                        instantiate (get_type_var x constraints env) , constraints
                    with Not_found -> TVar("type_"^x), add_constraint (x, TVar("type_"^x)) constraints
                end
            | Apply(u1,u2) ->
                begin
                    let t1,constraints = aux u1 constraints in
                    let t2,constraints = aux u2 constraints in
                    let sigma1= unify_type t1 (instantiate (Arrow(TVar("'x"),TVar("'y")))) in
                    let constraints = List.map (second (subst_type sigma1)) constraints in
                    let t1 = subst_type sigma1 t1 in
                    let t2 = subst_type sigma1 t2 in
                    match t1 with
                        | Arrow(t11,t12) ->
                                let sigma2 = unify_type t11 t2 in
                                let constraints = List.map (second (subst_type sigma2)) constraints in
(* print_string "constraints2, after "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) constraints2; print_newline(); *)

                                (try
                                    subst_type sigma2 t12 , constraints
                                with Error s -> raise (Error ("cannot type this term: " ^ s)))
                        | _ -> raise @$ Error ("not a function type!!!")
                end

    in aux u vars








