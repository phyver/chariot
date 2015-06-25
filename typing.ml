(*
 * operations on type and type inference
 *)
open Misc
open Base
open State
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
    try
        let sigma = unify_type_mgu t1 t2 in
        t1 = subst_type sigma t1
    with UnificationError _ -> false

(* add one constraint into a sorted list of constraints *)
let rec add_constraint (x,t) constraints = match constraints with
    | [] -> [(x,t)]
    | (y,s)::_ when x<y -> (x,t)::constraints
    | (y,s)::constraints when x>y -> (y,s)::(add_constraint (x,t) constraints)
    | (y,s)::constraints (* when x=y *) -> (x,unify_type s t)::constraints

(* merge two sorted lists of constraints *)
let merge_constraints cs1 cs2 =
    let rec merge_constraints_aux cs1 cs2 sigma = match cs1,cs2 with
        | [],cs | cs,[] -> cs,sigma
        | (x1,t1)::cs1, (x2,_)::_ when x1<x2 ->
            let cs,sigma = merge_constraints_aux cs1 cs2 sigma in
            (x1,t1)::cs , sigma
        | (x1,_)::_, (x2,t2)::cs2 when x1>x2 ->
            let cs,sigma = merge_constraints_aux cs1 cs2 sigma in
            (x2,t2)::cs , sigma
        | (x1,t1)::cs1, (x2,t2)::cs2 (*when x1=x2*) ->
            let cs,sigma = merge_constraints_aux cs1 cs2 sigma in
            let tau = unify_type_mgu t1 t2 in
            (x1,subst_type tau t1)::cs , tau @ (List.map (second (subst_type tau)) sigma)
    in
    let cs,sigma = merge_constraints_aux cs1 cs2 [] in
    List.map (second (subst_type sigma)) cs

(* infers most general type of "u" in environment "env"
 *   - "constraints" contains the type of some free variables (the function
 *     being defined for exemple)
 *   - "sigma" contains some type substitution that we need to apply
 *
 * the result is the type of the term together with
 *   - the updated types of the free variables: we can discover new free
 *     variables, or discover some new constraints on existing variables
 *   - the updated list of type substitutions: we can discover that type 'x is
 *     supposed to be nat.
 *)
let infer_type (env:environment)
               (v:term)
               (constraints:(var_name*type_expression) list)    (* constraints for the types of free variables *)
               (sigma:(type_name*type_expression) list)         (* all the type substitution that need to be applied *)
  : type_expression * (var_name*type_expression) list * (type_name*type_expression) list
  = message 2 (fun _ -> print_string "infering type for ";
                        print_term v; print_newline());

    let rec infer_type_aux (v:term) constraints sigma
      : type_expression * (var_name*type_expression) list * (type_name*type_expression) list
      =
        message 4 (fun () ->
            print_string "infering type of (recursive call) ";
            print_term v;
            print_string "\n\t\twith constraints ";
            print_list "none" "" " , " "" (function x,t -> print_string (x^":"); print_type t) constraints;
            print_string "\n\t\tand types ";
            print_list "none" "" " , " "\n" (function x,t -> print_string ("'"^x^"="); print_type t) sigma;
            print_newline()
        );
        match v with
            | Angel -> instantiate_type (TVar("angel")) , constraints, sigma
            | Var(x) ->
                begin
                    try List.assoc x constraints, constraints, sigma
                    with Not_found ->
                        begin
                            try
                                let t = get_function_type env x in
                                (instantiate_type t, constraints, sigma)
                            with Not_found -> let t = TVar("type_"^x) in (t, add_constraint (x,t) constraints, sigma)
                        end
                end
            | Const(c,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        let p = get_constant_priority env c in
                        if p mod 2 = 0 then typeError (c ^ " is not a constructor");    (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [])
                    with Not_found -> typeError ("cannot infer type of constant " ^ c)
                end
            | Proj(d,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        let p = get_constant_priority env d in
                        if p mod 2 = 1 then typeError (d ^ " is not a destructor");     (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [])
                    with Not_found -> typeError ("cannot infer type of constant " ^ d)
                end
            | App(v1,v2) ->
                begin
                    let tv1,constraints,sigma = infer_type_aux v1 constraints sigma in
                    let tv2,constraints,sigma = infer_type_aux v2 constraints sigma in
                    let tfunc = instantiate_type (Arrow(TVar("arg"),TVar("result"))) in
                    let tau = unify_type_mgu tfunc tv1 in
                    let sigma = tau @ (List.map (second (subst_type tau)) sigma) in
                    let tfunc = subst_type sigma tfunc in
                    let targ,tres = match tfunc with
                        | Arrow(t1,t2) -> t1,t2
                        | _ -> assert false
                    in
                    (* NOTE: do not swap the arguments of unify_type_mgu below!!! TODO: understand... *)
                    let tau = unify_type_mgu targ tv2 in
                    let sigma = tau @ (List.map (second (subst_type tau)) sigma) in
                    let constraints = List.map (second (subst_type sigma)) constraints in
                    let tres = subst_type sigma tres in
                    tres,constraints,sigma
                end
            | Special v -> v.bot
    in
    let t,constraints,sigma = infer_type_aux v constraints [] in
    message 3 (fun () ->
        print_string "infered type of ";
        print_term v;
        print_string " : ";
        print_type t;
        print_string "\n\t\twith constraints ";
        print_list "none" "" " , " "" (function x,t -> print_string (x^":"); print_type t) constraints;
        print_string "\n\t\tand types ";
        print_list "none" "" " , " "\n" (function x,t -> print_string ("'"^x^"="); print_type t) sigma;
        print_newline()
    );
    t,constraints,sigma

