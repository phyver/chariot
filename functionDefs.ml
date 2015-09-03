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


open Env
open Utils
open Misc
open State
open Pretty
open StructPattern
open Typing
open Coverage
open Priorities
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

(* check that all the constructors are fully applied in a pattern *)
let rec check_constructor_arity env (v:'t term) : unit
  = match get_head v,get_args v with
        | Var _,args -> List.iter (check_constructor_arity env) args
        | Proj _,v::args -> List.iter (check_constructor_arity env) (v::args)
        | Proj _,[] -> assert false
        | App _,_ -> assert false
        | Const(c,_,_), args ->
            begin
                try
                    if (List.length args) <> get_constant_arity env c
                    then error (fmt "the subterm %s starts with a constructor that is not fully applied" (string_of_plain_term v));
                    List.iter (check_constructor_arity env) args
                with Not_found -> error (fmt "constructor %s doesn't exist in the environment" c)
            end
        | Angel _,_ | Daimon _,_ | Sp _,_ -> ()

(* check that a term has the shape of a lhs pattern *)
let check_lhs (v:'t term) : unit
  =
    let rec check_constructors v
      = match get_head v,get_args v with
            | Var _,[] -> ()
            | Var _,_ -> error "no function application is allowed inside constructor pattern"
            | Proj _,[] -> ()
            | Proj _,_ -> error "no projection is allowed inside constructor patterns"
            | App _,_ -> assert false
            | Const _, args -> List.iter check_constructors args
            | Angel _,_ -> error "no angel is allowed inside constructor patterns"
            | Daimon _,_ -> error "no daimon is allowed inside constructor patterns"
            | Sp(s,_),_ -> s.bot
            (* | Sp(Struct fields,_), [] -> List.iter (function _,v -> check_constructors v) fields *)
            (* | Sp(Struct _,_), _ -> error "structures cannot be applied" *)
    in
    match explode v with
        | (Var(f,()))::pats ->
            List.iter check_constructors pats
        | [] -> assert false
        | u::_ -> error (fmt "lhs of definition cannot start with %s" (string_of_plain_term u))

let check_clause env (funs: var_name list) (f:var_name) (lhs:'t term) (rhs:'t term) : unit
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
    (match find_common funs variables with
        | None -> ()
        | Some x -> error (fmt "you cannot have a variable with same name as one of the defined function (%s)" x));

    (* check that constructors are fully applied *)
    check_constructor_arity env lhs


let process_function_defs (env:environment)
                          (* (defs:(var_name * type_expression option * ('t pattern * 't term) list) list) *)
                          (* TODO: check types *)
                          defs
  : environment
  =

    (* remove structures *)
    let defs =
        if option "allow_structs"
        then remove_struct_defs defs
        else
            List.map
                (function f,t,clauses ->
                    let clauses = List.map
                                    (function lhs,rhs ->
                                        map_raw_term (fun _ -> error "no structure allowed") id id lhs ,
                                        map_raw_term (fun _ -> error "no structure allowed") id id rhs
                                    )
                                    clauses in
                    f,t,clauses)
                defs
    in

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    (* check clauses *)
    List.iter (function f,_,clauses ->
        List.iter (function (lhs,rhs) -> check_lhs lhs ; check_clause env new_functions f lhs rhs)
        clauses)
    defs;

    let defs = infer_type_defs env defs in
    if (verbose 1)
    then msg "Typing for %s successful" (string_of_list ", " id new_functions);

    (* check that the types of all subterms are consistant *)
    assert (
        List.iter (function f,t,clauses ->
            List.iter (function lhs,rhs -> ignore (type_of lhs) ; ignore (type_of rhs)
                    ) clauses
                  ) defs;
        true
    );

    let defs = if option "use_priorities"
               then infer_priorities env defs
               else defs
    in
    (* TODO: check that all priorities are > 0 and remove the instance of option "use_priorities" *)

    (* List.iter (function f,t,cls -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         print_typed_subterms lhs; *)
    (*         print_string "\n     ==>\n\n"; *)
    (*         print_typed_subterms rhs; *)
    (*         print_newline() *)
    (*     ) *)
    (*     cls *)
    (* ) defs; *)



    (* check completeness of pattern matching *)
    let defs = List.map
        (function f,t,clauses ->
            let f,clauses,args,cs = case_struct_of_clauses env f t clauses in
            if is_exhaustive f args cs
            then (if (verbose 1) then msg "the definition for %s is complete" f)
            else
                if option "allow_incomplete_defs"
                then warning "the definition for %s is incomplete" f
                else error (fmt "the definition for %s is incomplete" f);
            f,t,clauses,(args,cs)
        )
        defs
    in

    let defs =
        if option "expand_clauses"
        then
            let new_defs = List.map (function f,t,_,(xs,pat) -> f, Some t, convert_cs_to_clauses f xs pat) defs in
            let new_defs = infer_type_defs env new_defs in
            let new_defs = infer_priorities env new_defs in
            List.map2 (fun f_orig f_new ->
                            let f,t,_,cs = f_orig in
                            let f',t',cls = f_new in
                            assert (f=f');
                            assert (t=t');
                            f,t,cls,cs) defs new_defs
        else defs
    in


    (* SCT *)
    if size_change_termination env defs
    then
        begin
            if verbose 1
            then msg "the definition%s %s %s provably correct"
                    (plural new_functions "" "s")
                    (string_of_list ", " id new_functions)
                    (plural new_functions "is" "are")
        end
    else
        begin
            if option "allow_inadequate_defs"
             then warning "the definition%s %s %s NOT provably correct (weight_bound: %d, depth_bound: %d)"
                        (plural new_functions "" "s")
                        (string_of_list ", " id new_functions)
                        (plural new_functions "is" "are")
                        current_state.bound
                        current_state.depth
             else error (fmt  "the definition%s %s %s NOT provably correct (weight_bound: %d, depth_bound: %d)"
                            (plural new_functions "" "s")
                            (string_of_list ", " id new_functions)
                            (plural new_functions "is" "are")
                            current_state.bound
                            current_state.depth)
        end;



    let defs =
        List.fold_left (fun functions f ->
            let f,_,clauses,cs = f in
            let t = List.assoc f (List.map (function f,t,_,_ -> f,t) defs) in
            (f,current_state.current_bloc+1,t,clauses,cs)::functions
        )
        []
        defs
    in

    if verbose 1
    then print_newline();

    current_state.current_bloc <- current_state.current_bloc + 1;

    (* TODO: remove *)
    { env with functions = defs @ env.functions }
