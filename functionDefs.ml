(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
totality checker for recursive definitions involving nested least and
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
open Typing
open Coverage
open Priorities
open SCPCalls
open SCPGraph

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
let rec check_constructor_arity env (v:(empty,'p,'t) raw_term) : unit
  = match get_head v,get_args v with
        | Var _,args -> List.iter (check_constructor_arity env) args
        | Proj _,v::args -> List.iter (check_constructor_arity env) (v::args)
        | Proj _,[] -> assert false
        | App _,_ -> assert false
        | Struct(fields,_,_),[] -> List.iter (function _,v -> check_constructor_arity env v) fields
        | Struct(_,_,_),_ -> assert false
        | Const(c,_,_), args ->
            begin
                try
                    if (List.length args) <> get_constant_arity env c
                    then error (fmt "the subterm %s starts with a constructor that is not fully applied" (string_of_plain_term v));
                    List.iter (check_constructor_arity env) args
                with Not_found -> error (fmt "constructor %s doesn't exist in the environment" c)
            end
        | Angel _,_ | Daimon _,_ -> ()
        | Sp(s,_),_ -> s.bot

(* check that a term has the shape of a lhs pattern *)
let check_lhs (v:(empty,'p,'t) raw_term) : unit
  =
    let rec check_constructors v
      = match get_head v,get_args v with
            | Var _,[] -> ()
            | Var _,_ -> error "no function application is allowed inside constructor pattern"
            | Proj _,[] -> ()
            | Proj _,_ -> error "no projection is allowed inside constructor patterns"
            | App _,_ -> assert false
            | Struct(fields,_,_),[] -> List.iter (function _,v -> check_constructors v) fields
            | Struct(fields,_,_),_ -> assert false
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

let check_clause env (funs: var_name list) (f:var_name) (lhs:(empty,'p,'t) raw_term) (rhs:(empty,'p,'t) raw_term) : unit
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


(* remove "fun ... -> ..." by adding auxiliary functions *)
let remove_funs (env:environment) (defs:(var_name * type_expression option * (plain_term * parsed_term) list) list)
  : (var_name * type_expression option * (plain_term * plain_term) list) list
  =
    let counter = ref 0 in
    let new_aux f =
        incr counter;
        let sub = if option "use_utf8" then string_of_sub !counter else fmt "_%d" !counter in
        fmt "_%s%s" f sub
    in

    let rec process_rhs (f:var_name) (xs:var_name list) (rhs:parsed_term) : plain_term * (var_name * (plain_term * parsed_term) list) list
      =
        match rhs with
            | Var(x,t) -> Var(x,t),[]
            | Const(c,p,t) -> Const(c,p,t),[]
            | Proj(d,p,t) -> Proj(d,p,t),[]
            | Daimon(t) -> Daimon(t),[]
            | Angel(t) -> Angel(t),[]
            | App(v1,v2) ->
                let v1,aux1 = process_rhs f xs v1 in
                let v2,aux2 = process_rhs f xs v2 in
                App(v1,v2), aux1@aux2
            | Struct(fields,p,t) ->
                let fields,aux_defs
                  = List.fold_right (fun dv r ->
                      let fields,aux_defs = r in
                      let d,v = dv in
                      let v,new_aux = process_rhs f xs v in
                      (d,v)::fields , new_aux@aux_defs
                    ) fields ([],[])
                in
                Struct(fields,p,t),aux_defs
            | Sp(Fun(ys,v),t) ->
                (* check that all y's are different *)
                (match find_dup ys with
                    | None -> ()
                    | Some y -> error (fmt "local function has duplicate argument %s" y));
                let xs = let ys = List.sort compare ys in diff_uniq xs ys in
                let xs = List.map (fun x -> Var(x,())) xs in
                let ys = List.map (fun x -> Var(x,())) ys in
                let args = xs @ ys in
                let f_aux = new_aux f in
                let f_aux_xs = app (Var(f_aux,())) xs in
                let aux_def = app (Var(f_aux,())) args, v in
                f_aux_xs,[f_aux,[aux_def]]
    in

    let process_clause (f:var_name) (cl:plain_term * parsed_term)
      : (plain_term*plain_term) * (var_name * (plain_term * parsed_term) list) list
      = let lhs,rhs = cl in
        let xs = List.sort compare (extract_pattern_variables lhs) in
        let rhs,aux_defs = process_rhs f xs rhs in
        (lhs,rhs), aux_defs
    in

    let process_function (f:var_name) (clauses:(plain_term * parsed_term) list)
      : (plain_term * plain_term) list * (var_name * (plain_term * parsed_term) list) list
      =
        counter := 0;
        let tmp = List.map (function lhs,rhs -> process_clause f (lhs,rhs)) clauses in
        let clauses,aux_defs = List.split tmp in
        let aux_defs = List.concat aux_defs in
        clauses, aux_defs
    in

    let rec process_functions  (defs:(var_name * type_expression option * (plain_term * parsed_term) list) list)
      : (var_name * type_expression option * (plain_term * plain_term) list) list
      =
        let tmp = List.map (function f,t,clauses -> let f_cls,aux_functions = process_function f clauses in (f,t,f_cls),aux_functions) defs in
        let defs,aux_defs = List.split tmp in
        let aux_defs = List.concat aux_defs in
        let aux_defs = List.map (function f_aux,cls -> f_aux,None,cls) aux_defs in
        match aux_defs with
            | [] -> defs
            | aux_defs -> defs @ (process_functions aux_defs)
    in

    process_functions defs


let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (parsed_term * parsed_term) list) list)
  : environment
  =

    (* check that the LHS of each clauses doesn't contain functions *)
    let defs:(var_name * type_expression option * (plain_term * parsed_term) list) list
      = List.map
            (function f,t,clauses ->
                let clauses =
                    List.map
                        (first (map_raw_term
                            (fun _sp ->
                                error (fmt "'fun' keyword not allowed in pattern for %s" f)) id id))
                        clauses
                in
                f,t,clauses)
            defs in

    (* remove "fun ... -> ..." by adding auxiliary functions *)
    let defs:(var_name * type_expression option * (plain_term * plain_term) list) list
      = remove_funs env defs in

    (* check that the functions are all different *)
    let new_functions = List.map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    (* check clauses *)
    List.iter (function f,_,clauses ->
        List.iter (function (lhs,rhs) -> check_lhs lhs ; check_clause env new_functions f lhs rhs)
        clauses)
    defs;

    (* infer type of definitions *)
    let (defs:(var_name * type_expression * (typed_term * typed_term) list) list)
      = infer_type_defs env defs in
    if (verbose 1)
    then msg "Typing for %s successful" (string_of_list ", " id new_functions);

    (* List.iter (function f,t,cls -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         debug " %s => %s" (string_of_typed_term lhs) (string_of_typed_term rhs) *)
    (*     ) *)
    (*     cls; *)
    (*     debug ""; *)
    (* ) defs; *)

    (* check that the types of all subterms are consistant *)
    assert (
        List.iter (function f,t,clauses ->
            List.iter (function lhs,rhs -> ignore (type_of lhs) ; ignore (type_of rhs)
                    ) clauses
                  ) defs;
        true
    );

    (* List.iter (function f,t,cls -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         debug " %s => %s" (string_of_term lhs) (string_of_term rhs) *)
    (*     ) *)
    (*     cls; *)
    (*     debug ""; *)
    (* ) defs; *)

    (* check completeness of pattern matching and compute CASE form of the definition *)
    let (defs:(var_name * type_expression * (typed_term * typed_term) list * case_struct_def) list)
      = List.map
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


    (* expand case_struct_def to clauses if relevant *)
    let (defs:(var_name * type_expression * (typed_term * typed_term) list * case_struct_def) list)
      = if option "expand_clauses"
        then
            let new_defs = List.map (function f,t,_,(xs,pat) -> f, Some t, convert_cs_to_clauses env f xs pat) defs in
            let new_defs = infer_type_defs env new_defs in
            List.map2 (fun f_orig f_new ->
                            let f,t,_,cs = f_orig in
                            let f',t',cls = f_new in
                            assert (f=f');
                            assert (t=t');
                            f,t,cls,cs) defs new_defs
        else defs
    in
    (* List.iter (function f,t,cls,(xs,cs) -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         debug " %s => %s" (string_of_plain_term lhs) (string_of_plain_term rhs) *)
    (*     ) *)
    (*     cls; *)
    (*     debug "CASE form %s" (string_of_case_struct_term cs); *)
    (* ) defs; *)

    (* infer priorities for definitions *)
    let (defs:(var_name * type_expression * function_clause list * case_struct_def) list)
      = infer_priorities env defs
    in

    (* List.iter (function f,t,cls,(xs,cs) -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         debug " %s => %s" (string_of_plain_term lhs) (string_of_plain_term rhs) *)
    (*     ) *)
    (*     cls; *)
    (*     debug "after simplification:\n    %s %s |--> %s" f (string_of_list " " id xs) (string_of_case_struct_term cs) *)
    (* ) defs; *)


    (* SCP *)
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
            if option "allow_unsafe_defs"
             then warning "the definition%s %s %s NOT provably total (weight_bound: %d, depth_bound: %d)"
                        (plural new_functions "" "s")
                        (string_of_list ", " id new_functions)
                        (plural new_functions "is" "are")
                        (get_int_option "bound")
                        (get_int_option "depth")
             else error (fmt  "the definition%s %s %s NOT provably total (weight_bound: %d, depth_bound: %d)"
                            (plural new_functions "" "s")
                            (string_of_list ", " id new_functions)
                            (plural new_functions "is" "are")
                            (get_int_option "bound")
                            (get_int_option "depth"))
        end;



    (* add the bloc number *)
    let (defs:(var_name * bloc_nb * type_expression * function_clause list * case_struct_def) list)
      = List.fold_left (fun functions f ->
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

    { env with functions = defs @ env.functions }
