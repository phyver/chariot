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
        | Some(f) -> error (fmt "function %s is defined more than once" f)

(* check that the function being defined are different from the functions in the environment *)
(* FIXME: can I remove this constraint easily? *)
let check_new_funs_different_from_old (new_funs:var_name list) (old_funs:var_name list) : unit
  = match find_common new_funs old_funs with
        | None -> ()
        | Some f -> error (fmt "function %s already exists" f)


let check_clause (funs: var_name list) (f:var_name) (lhs:pattern) (rhs:term) : unit
  =
    (* get function from LHS and check it is equal to f *)
    let _f = get_function_name lhs in
    if not (_f = f) then error (fmt "function names %s and %s do not match" f _f);

    (* get variables *)
    let variables = extract_pattern_variables lhs in
    (match find_dup variables with
        | None -> ()
        | Some(x) -> error (fmt "pattern is not linear: variable %s appears more than once" x));


    (* check that the variables appearing in a pattern are different from the function names being defined *)
    (* FIXME: can I remove this constraint easily? *)
    match find_common funs variables with
        | None -> ()
        | Some x -> error (fmt "you cannot have a variable with same name as one of the defined function (%s)" x)


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

    (* check clauses *)
    List.iter (function f,_,clauses ->
        List.iter (function (lhs,rhs) -> check_clause new_functions f lhs rhs)
        clauses)
    defs;


    let defs = infer_type_defs env defs in

    (* List.iter (function f,t,cls -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         print_typed_subterms lhs; *)
    (*         print_string "\n     ==>\n\n"; *)
    (*         print_typed_subterms rhs; *)
    (*         print_newline() *)
    (*     ) *)
    (*     cls *)
    (* ) defs; *)


    (* (1* check completeness of pattern matching *1) *)
    (* if option "check_completeness" *)
    (* then *)
    (*     List.iter (function f,_,clauses -> *)
    (*             if not (check_exhaustivity env clauses) *)
    (*             then error ("function " ^ f ^ " is not complete")) *)
    (*         defs; *)


    let defs = if option "use_priorities"
               then infer_priorities env defs
               else defs
    in

(*     (1* (2* SCT *2) *1) *)
(*     (1* if option "check_adequacy" *1) *)
(*     (1* then *1) *)
(*     (1*     begin *1) *)
(*     (1*         let graph = callgraph_from_definitions defs *1) *)
(*     (1*         in *1) *)
(*     (1*         let graph = if option "collapse_graph" then collapse_graph current_state.bound current_state.depth graph else graph in *1) *)
(*     (1*         if size_change_termination graph *1) *)
(*     (1*         then msg "the functions are correct" *1) *)
(*     (1*         else msg "the functions are NOT provably correct" *1) *)
(*     (1*     end; *1) *)



    let defs =
        List.fold_left (fun functions f ->
            let f,_,clauses = f in
            let t = List.assoc f (List.map (function f,t,_ -> f,t) defs) in
            (f,current_state.current_function_bloc+1,t,clauses)::functions
        )
        []
        defs
    in

    current_state.current_function_bloc <- current_state.current_function_bloc + 1;

    (* TODO: remove *)
    let functions = List.map (function f,n,t,cls -> f,n,t,List.map (function lhs,rhs -> (map_type_term (fun _ -> ()) lhs, map_type_term (fun _ -> ()) rhs)) cls) defs in
    { env with functions = functions @ env.functions }
