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


open Base
open Misc
open State
open Pretty
open Typing
open CheckCoverage
open InferPriorities
open SCTCalls
open SCTGraph

(* check that a type is correct *)
let rec check_type (env:environment) (t:type_expression) : unit
  = match t with
    | TVar _ -> ()
    | Arrow(t1,t2) -> check_type env t1 ; check_type env t2
    | Data(tname,_) -> try ignore (is_inductive env tname) with Not_found -> error (fmt "type %s doesn't exist" tname)

(* check that all the functions are different *)
let check_uniqueness_functions (funs:var_name list) : unit
  = match find_dup funs with
        | None -> ()
        | Some(f) -> error ("function " ^ f ^ " is defined more than once")

let check_new_funs_different_from_old (new_funs:var_name list) (old_funs:var_name list) : unit
  = match find_common new_funs old_funs with
        | None -> ()
        | Some f -> error ("function " ^ f ^ " already exists")


let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (term * term) list) list)
  : environment
  =

    (* TODO: I shouldn't look at the types of functions anywhere but should
     * keep accumulating constraints about the functions type, and check that
     * they coincide with the given types at the very end *)

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    (* TODO: move into typing.ml *)
    (* gather the constraints on the functions by looking at a single clause *)
    let type_single_clause (f:var_name) (lhs_pattern,rhs_term:pattern*term) 
      : (var_name*type_expression) list * type_expression list
      =
        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then error ("function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let lhs_vars = extract_term_variables lhs_pattern in
        (match find_dup lhs_vars with
            | None -> ()
            | Some(x) -> error ("pattern is not linear: variable " ^ x ^ " appears more than once"));

        (* infer type and gather datatypes *)
        let constraints,datatypes = infer_type_clause env lhs_pattern rhs_term in

        (* remove constraints on pattern variables *)
        let constraints = List.filter (function x,_ -> (x = f) || (not (List.mem x lhs_vars))) constraints in

        (* check that all the variables appearing on the RHS were also on the LHS *)
        List.iter (function x,t ->
                    if not (List.mem x new_functions)
                    then error (x ^ " is free!")
                  ) constraints;

       constraints,datatypes
    in

    (* TODO: move into typing.ml and rename to type_several_clauses *)
    let rec process_defs constraints datatypes = function
        | [] -> constraints, datatypes
        | (f,k,[])::defs -> process_defs constraints datatypes defs
        | (f,k,clause::clauses)::defs ->
            let rconstraints,rdatatypes = process_defs constraints datatypes ((f,k,clauses)::defs) in
            let constraints,datatypes = type_single_clause f clause in
            let constraints, sigma = merge_constraints rconstraints constraints in
            let datatypes = uniq (List.map (subst_type sigma) (datatypes @ rdatatypes)) in
            (constraints , datatypes)
    in

    (* TODO: move into typing.ml *)
    reset_fresh_variable_generator [];
    let constraints,datatypes = process_defs [] [] defs in

    (* TODO: move into typing.ml *)
    (* check that the types given by the user are compatible with the infered types *)
    reset_fresh_variable_generator (datatypes@(List.map snd constraints));
    (* we try to unify the types given by the user and the infered types,
     * uniformly for all the functions in the bloc *)
    let subst_coercion f t constraints datatypes
      = let infered = List.assoc f constraints in
        match t with
            | None -> constraints,datatypes
            | Some t -> 
                check_type env t;
                let new_t = instantiate_type t in
                try
                    let sigma = unify_type_mgu new_t infered in
                    (List.map (second (subst_type sigma)) constraints , List.map (subst_type sigma) datatypes)
                with UnificationError _ -> error ("function "^f^" cannot be coerced to type "^(string_of_type t))
    in
    (* that's the corresponding substitution: it instantiate the infered types to the given types (with different variables though) *)
    let constraints,datatypes = List.fold_left
                        (fun cd f ->
                            let constraints,datatypes = cd in
                            let f,t,_ = f in
                            subst_coercion f t constraints datatypes)
                        (constraints,datatypes)
                        defs
    in


    let functions =
        List.fold_left (fun functions f ->
            let f,_,clauses = f in
            let t = List.assoc f constraints in
            (f,t,clauses)::functions
        )
        []
        defs
    in

    (* choose the substitution that will make the final type of the definition a good choice:
     *   - either use the given type
     *   - or rename the type variables
     *)
    let choose_type f t =
        let infered = List.assoc f constraints in
        match t with
        | None ->
            reset_fresh_variable_generator [];
            instantiate_type infered
        | Some t ->
            reset_fresh_variable_generator [t];
            let infered_new = instantiate_type infered in
            if (equal_type t infered_new)
            then t
            else error ("function " ^ f ^ " is coerced to type " ^ (string_of_type t) ^ " which is not an instance of " ^ (string_of_type infered_new) ^ "...")
    in

    (* check completeness of pattern matching *)
    if option "check_completeness"
    then
        List.iter (function f,_,clauses ->
                if not (check_exhaustivity env clauses)
                then error ("function " ^ f ^ " is not complete"))
            defs;


    let functions = if option "use_priorities"
                    then infer_priorities env functions datatypes
                    else functions
    in


    (* SCT *)
    if option "check_adequacy"
    then
        begin
            let graph = callgraph_from_definitions functions
            in
            let graph = if option "collapse_graph" then collapse_graph current_state.bound current_state.depth graph else graph in
            if size_change_termination graph
            then msg "the functions are correct"
            else msg "the functions are NOT provably correct"
        end;


    let functions =
        List.fold_left (fun functions f ->
            let f,_,clauses = f in
            let t = List.assoc f (List.map (function f,t,_ -> f,t) defs) in
            (f,current_state.current_function_bloc+1,choose_type f t,clauses)::functions
        )
        []
        functions
    in

    current_state.current_function_bloc <- current_state.current_function_bloc + 1;

    { env with functions = functions @ env.functions }
