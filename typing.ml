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
let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression
  = match t with
    | TVar (y) -> (try List.assoc y sigma with Not_found -> t)
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t2)
    | Data(tname, args) -> Data(tname, List.map (subst_type sigma) args)

let rec subst_type_term  (sigma:type_substitution) (u:(empty,type_expression) special_term) : (empty,type_expression) special_term
  = match u with
        | Angel(t) -> Angel(subst_type sigma t)
        | Var(x,t) -> Var(x,subst_type sigma t)
        | Const(c,p,t) ->  Const(c,p,subst_type sigma t)
        | Proj(d,p,t) ->  Proj(d,p,subst_type sigma t)
        | App(u1,u2,t) ->
            let u1 = subst_type_term sigma u1 in
            let u2 = subst_type_term sigma u2 in
            let t = subst_type sigma t in
            App(u1,u2,t)
        | Special(s,t) -> s.bot


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

(* instantiate all the variables from a type with fresh variables *)
let instantiate_type (t:type_expression) : type_expression =
    let vars = extract_type_variables t in
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

(* merge 2 lists of constraints and return the corresponding substitution *)
let merge_constraints (cs1:(var_name*type_expression) list) (cs2:(var_name*type_expression) list)
    :(var_name*type_expression) list * (type_name*type_expression) list
  =
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
            | Angel _ -> instantiate_type (TVar("angel")) , constraints, sigma, datatypes
            | Var(x,_) ->
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
            | Const(c,_,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        if is_projection env c then typeError (c ^ " is not a constructor");    (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [], (get_result_type t)::datatypes)
                    with Not_found -> typeError ("cannot infer type of constant " ^ c)
                end
            | Proj(d,_,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        if not (is_projection env d) then typeError (d ^ " is not a destructor");     (* FIXME: this should be done by a check_term function *)
                        (t , constraints, [], (get_first_arg_type t)::datatypes)
                    with Not_found -> typeError ("cannot infer type of constant " ^ d)
                end
            | App(v1,v2,_) ->
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
            | Special(v,_) -> v.bot
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



   (* ============================================================================== *)




let infer_type_new (env:environment)
               (v:('empty,'t) special_term)
               (constraints:(var_name*type_expression) list)    (* constraints for the types of free variables *)
  : type_expression * (empty,type_expression) special_term * (var_name*type_expression) list * (type_name*type_expression) list
  = if verbose 2 then debug "infering type for %s" (string_of_term v);

    let rec infer_type_aux (v:(empty,'t) special_term) constraints
      : type_expression * (empty,type_expression) special_term * (var_name*type_expression) list * (type_name*type_expression) list
      (* : type_expression * (var_name*type_expression) list * (type_name*type_expression) list *)
      =
          if verbose 4
          then (
            debug "infering type of (recursive call) %s" (string_of_term v);
            debug "\twith constraints %s" (string_of_list" , " (function x,t -> x^":"^(string_of_type t)) constraints);
            print_newline()
        );
        match v with
            | Angel _ ->
                let t = instantiate_type (TVar("angel")) in
                t, Angel(t), constraints, []
            | Var(x,_) ->
                begin
                    try let t = List.assoc x constraints in
                    t, Var(x,t), constraints, []
                    with Not_found ->
                        begin
                            try
                                let t = get_function_type env x in
                                let t = instantiate_type t in
                                (t, Var(x,t), constraints, [])
                            with Not_found -> let t = instantiate_type (TVar("type_"^x)) in (t, Var(x,t), add_constraint (x,t) constraints, [])
                        end
                end
            | Const(c,p,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        if is_projection env c then typeError (c ^ " is not a constructor");    (* FIXME: this should be done by a check_term function *)
                        (t, Const(c,p,t) , constraints, [])
                    with Not_found -> typeError ("cannot infer type of constant " ^ c)
                end
            | Proj(d,p,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        if not (is_projection env d) then typeError (d ^ " is not a destructor");     (* FIXME: this should be done by a check_term function *)
                        (t, Proj(d,p,t) , constraints, [])
                    with Not_found -> typeError ("cannot infer type of constant " ^ d)
                end
            | App(v1,v2,_) ->
                begin
                    let t1,v1,constraints,sigma1 = infer_type_aux v1 constraints in
                    let t2,v2,constraints,sigma2 = infer_type_aux v2 constraints in
                    (* debug "sigma1: %s" (string_of_type_substitution sigma1); *)
                    (* debug "sigma2: %s" (string_of_type_substitution sigma2); *)

                    let tfunc = instantiate_type (Arrow(TVar("arg"),TVar("result"))) in
                    let sigma3 = unify_type_mgu tfunc t1 in
                    (* debug "sigma3: %s" (string_of_type_substitution sigma3); *)
                    let tfunc = subst_type sigma3 tfunc in

                    let targ,tres = match tfunc with
                        | Arrow(a,b) -> a,b
                        | _ -> assert false
                    in

                    (* NOTE: do not swap the arguments of unify_type_mgu below!!! TODO: understand... *)
                    let tau = unify_type_mgu targ t2 in
                    (* debug "tau: %s" (string_of_type_substitution tau); *)
                    let sigma = sigma1 @ sigma2 @ sigma3 in

                    let sigma = tau @ (List.map (second (subst_type tau)) sigma) in
                    (* debug "sigma: %s" (string_of_type_substitution sigma); *)
                    let constraints = List.map (second (subst_type sigma)) constraints in
                    let tres = subst_type sigma tres in
                    tres,App(v1,v2,tres),constraints,sigma
                end
            | Special(v,_) -> v.bot
    in
    let t,v,constraints,sigma = infer_type_aux v constraints in
    let v = subst_type_term sigma v in
    if verbose 3
    then (
        debug "infered type of %s : %s" (string_of_term v) (string_of_type t);
        debug "\twith free variables: %s" (string_of_list " , " (function x,t -> x^":"^(string_of_type t)) constraints);
        debug "\tand types: %s" (string_of_list " , " (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
        print_newline()
    );

    let v = subst_type_term sigma v in

    t,v,constraints,sigma

let infer_type_term_new (env:environment) (v:(empty,'t) special_term)
  : type_expression * (empty,type_expression) special_term * (var_name*type_expression) list
  = reset_fresh_variable_generator [];
    let t,v,constraints,_ = infer_type_new env v [] in
    t,
    v,
    constraints

let infer_type_term env v
  = let t,v,constraints = infer_type_term_new env v in
    (* print_typed_subterms v; *)
    t,constraints

let infer_type_clause_new (env:environment)
                          (constraints:(var_name*type_expression) list)     (* should contain constraints for __ALL__ the functions *)
                          (lhs_pattern:(empty,'t) special_term)
                          (rhs_def:(empty,'t) special_term)
  : (var_name*type_expression) list * (empty,type_expression) special_term * (empty,type_expression) special_term
  =

    let funs = List.map fst constraints in

    (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
    (* reset_fresh_variable_generator []; *)
    (* I need to reset the generator only once for each bunch of recursive definitions. Otherwise, there can be some interference between clauses, like
        val test1 x = []
          | test1 [] = []
    *)
    let infered_type_lhs, lhs_pattern, constraints_lhs,sigma = infer_type_new { env with functions=[] } lhs_pattern constraints in

    let variables = extract_pattern_variables lhs_pattern in

    (* print_typed_subterms lhs_pattern; *)

    (* infer type of RHS *)
    let infered_type_rhs, rhs_def, constraints,sigma = infer_type_new env rhs_def constraints_lhs in
    (* print_typed_subterms rhs_def; *)

    (* unify types of LHS and RHS *)
    let tau = unify_type_mgu infered_type_rhs infered_type_lhs in
    let sigma = tau @ (List.map (second (subst_type tau)) sigma) in

    (* update constraints ant types of lhs/rhs *)
    let constraints = List.map (second (subst_type sigma)) constraints in
    let lhs_pattern = subst_type_term sigma lhs_pattern in
    let rhs_def = subst_type_term sigma rhs_def in
    (* print_typed_subterms lhs_pattern; *)

    (* remove variables from constraints *)
    let constraints = List.filter (function x,t -> not (List.mem x variables)) constraints in

    (* check that no remaining variables is left *)
    List.iter (function f,_ -> if not (List.mem f funs) then error (fmt "variable %s is free" f)) constraints;

    if verbose 4
    then (
        debug "infered type of pattern: %s" (string_of_type infered_type_lhs);
        debug" and infered type of definition: %s" (string_of_type infered_type_rhs);
        debug "\tgiving %s" (string_of_type (subst_type sigma infered_type_rhs));
        debug "\ttypes: %s" (string_of_list "," (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
        debug "\twith constraints: %s" (string_of_list "," (function x,t -> x^":"^(string_of_type t)) constraints);
        );

    (* the type of the RHS should be an instance of the type of the LHS *)
    (* oups: val s.Tail = ??? doesn't work with this... *)
    (* if not (infered_type_rhs = subst_type sigma infered_type_rhs) *)
    (* then error ("rhs and lhs do not have the same type"); *)

   constraints, lhs_pattern,rhs_def


(* let infer_type_clause env (lhs_pattern:pattern) (rhs_def:term) *)
(*   : (var_name*type_expression) list * type_expression list *)
(*   = let sigma,lhs,rhs = infer_type_clause_new env [] lhs_pattern rhs_def in *)
(*     let datatypes = merge_uniq (extract_datatypes_from_typed_term lhs) (extract_datatypes_from_typed_term rhs) in *)

(*     debug  "\tencountered datatypes: %s" (string_of_list " , " string_of_type datatypes); *)
(*     sigma, datatypes *)


let infer_type_defs
    (env:environment)
    (defs:(var_name * type_expression option * ((empty,'t) special_term * (empty,'t) special_term) list) list)
    : (var_name * type_expression * (((empty,type_expression) special_term * (empty,type_expression) special_term)) list) list
  =
    reset_fresh_variable_generator [];

    (* all the clauses *)
    let clauses = List.concat (List.map (function f,_,clauses -> (List.map (function lhs,rhs -> f,lhs,rhs) clauses)) defs) in

    (* the types of functions, as given by the user *)
    let given_types = List.sort compare (List.concat (List.map (function f,t,_ -> match t with None -> [] | Some t -> [f,t]) defs)) in

    (* initial constraints on the functions *)
    let initial_constraints = List.sort compare (List.map (function f,t,_ -> match t with None -> (f,TVar("type_"^f)) | Some t -> (f,t)) defs) in

    let all_constraints,clauses = List.split (
        List.map
            (function f,lhs,rhs ->
                let constraints = List.map (second instantiate_type) initial_constraints in
                let constraints, lhs,rhs = infer_type_clause_new env constraints lhs rhs in
                (constraints, (f,lhs,rhs))
            )
            clauses)
    in

    let constraints,sigma =
        List.fold_left
            (fun r constraints ->
                let constraints',sigma' = r in
                let constraints,sigma = merge_constraints constraints constraints' in
                let sigma = sigma @ (List.map (second (subst_type sigma)) sigma') in
                constraints,sigma
                )
            ([],[])
            all_constraints
    in

    let clauses = List.map (function f,lhs,rhs -> (f,subst_type_term sigma lhs,subst_type_term sigma rhs)) clauses in

    (* simplify type variables *)
    let tvars = uniq (List.concat (List.map (function _,t -> extract_type_variables t) constraints)) in
    reset_fresh_variable_generator [];
    let sigma = List.map (fun x -> x,instantiate_type (TVar x)) tvars in
    let clauses = List.map (function f,lhs,rhs -> (f,subst_type_term sigma lhs,subst_type_term sigma rhs)) clauses in

    (* putting everything back together *)
    let clauses = partition (function f,lhs,rhs -> f) clauses in
    let clauses = List.map
                    (fun cls ->
                        try
                            let f,_,_ = List.hd cls in
                            f,List.map (function _,lhs,rhs -> lhs,rhs) cls
                        with Failure "hd" -> assert false
                    )
                    clauses in


    (* chooses appropriate type to show the user *)
    let choose_type f =
        try
            let tf = List.assoc f given_types in
            reset_fresh_variable_generator [tf];
            let t = instantiate_type (List.assoc f constraints) in
            if is_instance tf t
            then tf
            else error (fmt "function %s cannot be coerced to type %s" f (string_of_type tf))
        with Not_found ->
            try
                let t = List.assoc f constraints in
                reset_fresh_variable_generator [];
                instantiate_type t
            with Not_found -> assert false
    in

    let clauses = List.map (function f,cls -> f,choose_type f,cls) clauses in

    clauses
