(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*)


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
let list_type_variables = ref []
let reset_fresh_variable_generator ts =
    fresh_variable_nb := 0;
    list_type_variables := uniq (List.concat (List.map extract_type_variables ts))
let fresh_variable () =
    let alpha = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] in
    let stop = ref false in
    let x = ref "" in
    while (not !stop)
    do
        let n = !fresh_variable_nb / 26 in
        let var = !fresh_variable_nb mod 26 in
        x := (List.nth alpha var) ^ (if n = 0 then "" else (string_of_int n));
        incr fresh_variable_nb;
        stop := not (List.mem !x !list_type_variables)
    done;
    list_type_variables := !x::!list_type_variables;
    TVar(!x)

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
    if verbose 4 then (debug "looking for mgu of %s and %s" (string_of_type t1) (string_of_type t2));

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

(* check if two types are equal, up to renaming of free variables *)
let equal_type t1 t2 = (is_instance t1 t2) && (is_instance t2 t1)

(* add one constraint into a sorted list of constraints *)
let rec add_constraint (x,t) constraints = match constraints with
    | [] -> [(x,t)]
    | (y,s)::_ when x<y -> (x,t)::constraints
    | (y,s)::constraints when x>y -> (y,s)::(add_constraint (x,t) constraints)
    | (y,s)::constraints (* when x=y *) -> (x,unify_type s t)::constraints

(* merge two sorted lists of constraints and returns the global substitution used while merging *)
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
    List.map (second (subst_type sigma)) cs, sigma

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
 *  - a list of datatypes that were used during inference (useful for putting
 *    priorities of constants for the termination checker)
 *)
let infer_type (env:environment)
               (v:term)
               (constraints:(var_name*type_expression) list)    (* constraints for the types of free variables *)
               (sigma:(type_name*type_expression) list)         (* all the type substitution that need to be applied *)
               (datatypes:type_expression list)
  : type_expression * (var_name*type_expression) list * (type_name*type_expression) list * type_expression list
  = if verbose 2 then debug "infering type for %s" (string_of_term v);

    let rec infer_type_aux (v:term) constraints sigma datatypes
      : type_expression * (var_name*type_expression) list * (type_name*type_expression) list * type_expression list
      =
          if verbose 4
          then (
            debug "infering type of (recursive call) %s" (string_of_term v);
            debug "\twith constraints %s" (string_of_list" , " (function x,t -> x^":"^(string_of_type t)) constraints);
            debug "\tand types %s" (string_of_list " , " (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
            print_newline()
        );
        match v with
            | Angel -> instantiate_type (TVar("angel")) , constraints, sigma, datatypes
            | Var(x) ->
                begin
                    try List.assoc x constraints, constraints, sigma, datatypes
                    with Not_found ->
                        begin
                            try
                                let t = get_function_type env x in
                                let t = instantiate_type t in
                                (t, constraints, sigma, datatypes)
                            with Not_found -> let t = TVar("type_"^x) in (t, add_constraint (x,t) constraints, sigma, datatypes)
                        end
                end
            | Const(c,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        if is_projection env c then typeError (c ^ " is not a constructor");    (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [], (get_result_type t)::datatypes)
                    with Not_found -> typeError ("cannot infer type of constant " ^ c)
                end
            | Proj(d,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        if not (is_projection env d) then typeError (d ^ " is not a destructor");     (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [], (get_first_arg_type t)::datatypes)
                    with Not_found -> typeError ("cannot infer type of constant " ^ d)
                end
            | App(v1,v2) ->
                begin
                    let tv1,constraints,sigma,datatypes = infer_type_aux v1 constraints sigma datatypes in
                    let tv2,constraints,sigma,datatypes = infer_type_aux v2 constraints sigma datatypes in
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
                    let datatypes = List.map (subst_type sigma) datatypes in
                    tres,constraints,sigma,datatypes
                end
            | Special v -> v.bot
    in
    let t,constraints,sigma,datatypes = infer_type_aux v constraints [] datatypes in
    let datatypes = uniq datatypes in
    if verbose 3
    then (
        debug "infered type of %s : %s" (string_of_term v) (string_of_type t);
        debug "\twith free variables: %s" (string_of_list " , " (function x,t -> x^":"^(string_of_type t)) constraints);
        debug "\tand types: %s" (string_of_list " , " (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
        debug "\tencountered atomic types: %s" (string_of_list " , " string_of_type datatypes);
        print_newline()
    );
    t,constraints,sigma,datatypes

let infer_type_term env v =
    reset_fresh_variable_generator [];
    let t,constraints,_,_ = infer_type env v [] [] [] in
    t,constraints

let infer_type_clause env (lhs_pattern:pattern) (rhs_def:term)
  : (var_name*type_expression) list * type_expression list
  =

    (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
    (* reset_fresh_variable_generator []; *)
    (* I need to reset the generator only once for each bunch of recursive definitions. Otherwise, there can be some interference between clauses, like
        val test1 x = []
          | test1 [] = []
    *)
    let infered_type_lhs, constraints_lhs,sigma,datatypes = infer_type { env with functions=[] } lhs_pattern [] [] [] in

    (* infer type of RHS *)
    let infered_type_rhs, constraints,sigma,datatypes = infer_type env rhs_def constraints_lhs sigma datatypes in

    (* unify types of LHS and RHS *)
    let tau = unify_type_mgu infered_type_rhs infered_type_lhs in
    let sigma = tau @ (List.map (second (subst_type tau)) sigma) in

    (* update constraints and datatypes *)
    let constraints = List.map (second (subst_type sigma)) constraints in
    let datatypes = uniq (List.rev_map (subst_type sigma) datatypes) in

    if verbose 4
    then (
        debug "infered type of pattern: %s" (string_of_type infered_type_lhs);
        debug" and infered type of definition: %s" (string_of_type infered_type_rhs);
        debug "\tgiving %s" (string_of_type (subst_type sigma infered_type_rhs));
        debug "\ttypes: %s" (string_of_list "," (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
        debug "\twith constraints: %s" (string_of_list "," (function x,t -> x^":"^(string_of_type t)) constraints);
        debug  "\tencountered datatypes: %s" (string_of_list " , " string_of_type datatypes)
        );

    (* the type of the RHS should be an instance of the type of the LHS *)
    (* oups: val s.Tail = ??? doesn't work with this... *)
    (* if not (infered_type_rhs = subst_type sigma infered_type_rhs) *)
    (* then error ("rhs and lhs do not have the same type"); *)

   constraints,datatypes

